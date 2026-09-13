import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Ramps

noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [Nonempty M] [I.Boundaryless]
variable {D : RealTimeInterval} {a b : ℝ} {N : ℕ}

theorem RampFamilyInput.exists_isSolutionOn_and_contMDiffOn_projection_slice
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ) {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (L : RampFamilyInput (I := I) (M := M) (D := D) (a := a) (b := b) (N := N) B lambda e)
    {c₀ : ProductCurve M} (hs₀ : c₀.SmoothOn (I := I) {a})
    (hr₀ : c₀.IsRampOn B.family.metric lambda {a})
    {c : ProductCurve M} (hs : c.SmoothOn (I := I) {a})
    (hr : c.IsRampOn B.family.metric lambda {a}) :
    ∃ sol : ProductCurve M,
      sol.IsSolutionOn B.family.metric lambda (Icc a b) ∧
        (∀ z, sol.map z a = c.map z a) ∧
        ContMDiffOn 𝓘(ℝ, ℝ) I ∞
          (fun z : ℝ => (sol.map (z : Surgery.Topology.Circle) a).1) univ := by
  obtain ⟨solFam, -, hsol⟩ := L.local_dependence c₀ hs₀ hr₀
  refine ⟨solFam c hs hr, (hsol c hs hr).1, (hsol c hs hr).2.2, ?_⟩
  have hsm : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞
      (fun p : ℝ × ℝ => (solFam c hs hr).projection.lift p.1 p.2)
      ((univ : Set ℝ) ×ˢ Icc a b) := (hsol c hs hr).1.smooth.1
  have hsub : (univ : Set ℝ) ×ˢ ({a} : Set ℝ) ⊆ univ ×ˢ Icc a b :=
    Set.prod_mono Subset.rfl (fun t ht => by
      rw [mem_singleton_iff] at ht
      rw [ht]
      exact ⟨le_rfl, B.lt.le⟩)
  have hrestrict := hsm.mono hsub
  have hz : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun z : ℝ => ((z, a) : ℝ × ℝ)) univ := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact contMDiffOn_id.prodMk contMDiffOn_const
  have hcomp := hrestrict.comp hz (fun z _ => ⟨mem_univ z, mem_singleton a⟩)
  refine hcomp.congr (fun z _ => ?_)
  simp only [Function.comp_apply, ProductCurve.projection, CurveMap.lift]

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
