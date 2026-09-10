import DifferentialGeometry.Analysis.Calculus.SmoothExtension.BorelHalfLine.Parametric
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Manifold

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

set_option backward.isDefEq.respectTransparency false in
theorem exists_contMDiff_extension_on_Icc {h : M × ℝ → F} {ρ : ℝ} (hρ : 0 < ρ)
    (hh : ContMDiffOn (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) ∞ h (univ ×ˢ Icc 0 ρ)) :
    ∃ g : M × ℝ → F, ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) ∞ g ∧
      EqOn g h (univ ×ˢ Icc 0 ρ) := by
  classical
  let T : M × ℝ → Set F := fun q ↦ if q.2 ∈ Icc 0 ρ then {h q} else univ
  have hT : ∀ q, Convex ℝ (T q) := by
    intro q
    dsimp only [T]
    split
    · exact convex_singleton _
    · exact convex_univ
  have hlocal : ∀ q : M × ℝ, ∃ U ∈ 𝓝 q, ∃ g : M × ℝ → F,
      ContMDiffOn (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) ∞ g U ∧ ∀ y ∈ U, g y ∈ T y := by
    intro q
    let c : OpenPartialHomeomorph M E :=
      { toPartialEquiv := extChartAt I q.1
        open_source := isOpen_extChartAt_source q.1
        open_target := isOpen_extChartAt_target q.1
        continuousOn_toFun := continuousOn_extChartAt q.1
        continuousOn_invFun := continuousOn_extChartAt_symm q.1 }
    have hq : q.1 ∈ c.source := mem_extChartAt_source q.1
    let f : ℝ → E → F := fun r z ↦ h (c.symm z, r)
    have hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc 0 ρ ×ˢ c.target) := by
      rw [← contMDiffOn_iff_contDiffOn]
      have hc' : ContMDiffOn 𝓘(ℝ, ℝ × E) I ∞ (fun z ↦ c.symm z.2)
          (Icc 0 ρ ×ˢ c.target) :=
        (contMDiffOn_extChartAt_symm (I := I) q.1).comp contDiff_snd.contMDiff.contMDiffOn (fun z hz ↦ hz.2)
      exact hh.comp (hc'.prodMk contDiff_fst.contMDiff.contMDiffOn) (fun z hz ↦ ⟨mem_univ _, hz.1⟩)
    obtain ⟨fext, V₀, hV₀, hfext, hext⟩ := DifferentialGeometry.Analysis.borel_interval_extend_param
      f ρ hρ c.target (c q.1) (by rw [c.open_target.interior_eq]; exact c.map_source hq) hf
    obtain ⟨V, hVV₀, hV, hqV⟩ := mem_nhds_iff.mp hV₀
    let A := c.source ∩ c ⁻¹' V
    have hA : IsOpen A := c.isOpen_inter_preimage hV
    have hqA : q.1 ∈ A := ⟨hq, hqV⟩
    let g : M × ℝ → F := fun y ↦ fext y.2 (c y.1)
    have hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c A :=
      (contMDiffOn_extChartAt (I := I) (x := q.1)).mono (fun z hz ↦ by
        have hz' : z ∈ (extChartAt I q.1).source := hz.1
        simpa only [extChartAt_source] using hz')
    have hc' : ContMDiffOn (I.prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞ (fun z ↦ c z.1) (A ×ˢ (univ : Set ℝ)) :=
      hc.comp contMDiffOn_fst (fun z hz ↦ hz.1)
    have hmap : ContMDiffOn (I.prod 𝓘(ℝ)) 𝓘(ℝ, ℝ × E) ∞
        (fun z ↦ (z.2, c z.1)) (A ×ˢ univ) := contMDiffOn_snd.prodMk_space hc'
    have hg : ContMDiffOn (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) ∞ g (A ×ˢ univ) :=
      hfext.contMDiffOn.comp hmap (fun z hz ↦ ⟨mem_univ _, hVV₀ hz.1.2⟩)
    refine ⟨A ×ˢ univ, (hA.prod isOpen_univ).mem_nhds ⟨hqA, mem_univ _⟩, g, hg, ?_⟩
    intro y hy
    dsimp only [T]
    split_ifs with hyr
    · change g y = h y
      change fext y.2 (c y.1) = h y
      rw [hext y.2 hyr (c y.1) (hVV₀ hy.1.2)]
      dsimp only [f]
      rw [c.left_inv hy.1.1]
    · exact mem_univ _
  obtain ⟨g, hg⟩ := exists_contMDiffMap_forall_mem_convex_of_local (I.prod 𝓘(ℝ)) hT hlocal
  refine ⟨g, g.contMDiff, ?_⟩
  intro q hq
  have h := hg q
  simpa only [T, if_pos hq.2, mem_singleton_iff] using h

end DifferentialGeometry.Topology.Manifold
