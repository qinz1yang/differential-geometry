import DifferentialGeometry.Geometry.Metric.Family.Product
import DifferentialGeometry.Geometry.Curvature.Product
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]

omit [I.Boundaryless] [J.Boundaryless] [T2Space M] [T2Space N] in
def SolutionOn.prod {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (T : SolutionOn (I := J) (M := N) D) :
    SolutionOn (I := I.prod J) (M := M × N) D where
  base.metric := fun t => (S.family.metric t).prod (T.family.metric t)

theorem hasDerivWithinAt_ricciFlow_prod
    (g : ℝ → SmoothRiemannianMetric I M) (h : ℝ → SmoothRiemannianMetric J N)
    {A : Set ℝ} {t : ℝ}
    (hg : ∀ x : M, ∀ u v : TangentSpace I x,
      HasDerivWithinAt (fun s => (g s).inner x u v)
        (-2 * ricciTensor (g t) x u v) A t)
    (hh : ∀ y : N, ∀ u v : TangentSpace J y,
      HasDerivWithinAt (fun s => (h s).inner y u v)
        (-2 * ricciTensor (h t) y u v) A t)
    (x : M × N) (u v : TangentSpace (I.prod J) x) :
    HasDerivWithinAt
      (fun s => ((g s).prod (h s)).inner x u v)
      (-2 * ricciTensor ((g t).prod (h t)) x u v) A t := by
  have h₁ := hg x.1 u.1 v.1
  have h₂ := hh x.2 u.2 v.2
  simp only [SmoothRiemannianMetric.prod_inner, ricciTensor_productMetric, mul_add]
  exact h₁.add h₂

theorem metric_hasDerivWithinAt_prod_of_isSolutionOn
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : SolutionOn (I := J) (M := N) D) (hT : IsSolutionOn T)
    {t : ℝ} (ht : t ∈ D.regular) (x : M × N)
    (u v : TangentSpace (I.prod J) x) :
    HasDerivWithinAt
      (fun s => ((S.family.metric s).prod (T.family.metric s)).inner x u v)
      (-2 * ricciTensor ((S.family.metric t).prod (T.family.metric t)) x u v)
      D.carrier t := by
  apply hasDerivWithinAt_ricciFlow_prod S.family.metric T.family.metric
  · intro y a b
    simpa only [SolutionOn.ricciAt, SolutionFamily.ricciAt,
      metricRicciAt_apply_eq_ricciTensor, SolutionOn.family_metric] using
      metric_derivWithin_eq_neg_two_ricci S hS ⟨t, ht⟩ y a b
  · intro y a b
    simpa only [SolutionOn.ricciAt, SolutionFamily.ricciAt,
      metricRicciAt_apply_eq_ricciTensor, SolutionOn.family_metric] using
      metric_derivWithin_eq_neg_two_ricci T hT ⟨t, ht⟩ y a b

private theorem scalar_continuousOn_prod_of_isSolutionOn
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : SolutionOn (I := J) (M := N) D) (hT : IsSolutionOn T) :
    ContinuousOn
      (fun p : ℝ × (M × N) => metricScalarAt
        ((S.family.metric p.1).prod (T.family.metric p.1)) p.2)
      (D.carrier ×ˢ (Set.univ : Set (M × N))) := by
  have hmap₁ : Continuous (fun p : ℝ × (M × N) => (p.1, p.2.1)) :=
    continuous_fst.prodMk (continuous_fst.comp continuous_snd)
  have hmap₂ : Continuous (fun p : ℝ × (M × N) => (p.1, p.2.2)) :=
    continuous_fst.prodMk (continuous_snd.comp continuous_snd)
  have hmaps₁ : Set.MapsTo (fun p : ℝ × (M × N) => (p.1, p.2.1))
      (D.carrier ×ˢ (Set.univ : Set (M × N))) (D.carrier ×ˢ Set.univ) :=
    fun p hp => ⟨hp.1, Set.mem_univ _⟩
  have hmaps₂ : Set.MapsTo (fun p : ℝ × (M × N) => (p.1, p.2.2))
      (D.carrier ×ˢ (Set.univ : Set (M × N))) (D.carrier ×ˢ Set.univ) :=
    fun p hp => ⟨hp.1, Set.mem_univ _⟩
  have h₁ := hS.scalarCont.comp hmap₁.continuousOn hmaps₁
  have h₂ := hT.scalarCont.comp hmap₂.continuousOn hmaps₂
  apply (h₁.add h₂).congr
  intro p hp
  exact metricScalarAt_productMetric (S.family.metric p.1) (T.family.metric p.1) p.2

private theorem scalar_differentiableWithinAt_prod_of_isSolutionOn
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : SolutionOn (I := J) (M := N) D) (hT : IsSolutionOn T)
    {t : ℝ} (ht : t ∈ D.carrier) (x : M × N) :
    DifferentiableWithinAt ℝ
      (fun s => metricScalarAt ((S.family.metric s).prod (T.family.metric s)) x)
      D.carrier t := by
  have h₁ := hS.scalarTime ht (Set.Subset.refl _) x.1
  have h₂ := hT.scalarTime ht (Set.Subset.refl _) x.2
  apply (h₁.add h₂).congr
  · intro s hs
    exact metricScalarAt_productMetric (S.family.metric s) (T.family.metric s) x
  · exact metricScalarAt_productMetric (S.family.metric t) (T.family.metric t) x

set_option backward.isDefEq.respectTransparency false in
private theorem ricci_continuousOn_prod_of_isSolutionOn
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : SolutionOn (I := J) (M := N) D) (hT : IsSolutionOn T) :
    tensor0SFamilyContinuousOnSet 2 D.carrier
      (fun t x => metricRicciAt ((S.family.metric t).prod (T.family.metric t)) x) := by
  have h₁ := tensor0SFamilyContinuousOnSet.pullback_of_contMDiff (I := I.prod J) (J := I)
    (fun t x => S.ricci t x) hS.ricciCont (Prod.fst : M × N → M) contMDiff_fst
  have h₂ := tensor0SFamilyContinuousOnSet.pullback_of_contMDiff (I := I.prod J) (J := J)
    (fun t x => T.ricci t x) hT.ricciCont (Prod.snd : M × N → N) contMDiff_snd
  apply (h₁.add h₂).congr
  intro t ht x
  apply ContinuousMultilinearMap.ext
  intro v
  simp only [mfderiv_fst, mfderiv_snd,
    SolutionOn.ricci, SolutionFamily.ricci_apply, SolutionFamily.ricciAt]
  change metricRicciAt (S.family.metric t) x.1 (fun k => (v k).1) +
      metricRicciAt (T.family.metric t) x.2 (fun k => (v k).2) =
    metricRicciAt ((S.family.metric t).prod (T.family.metric t)) x v
  have hv : v = vec2 (I := I.prod J) (x := x) (v 0) (v 1) := by
    ext k
    fin_cases k <;> rfl
  have hv₁ : (fun k => (v k).1) = vec2 (I := I) (x := x.1) (v 0).1 (v 1).1 := by
    ext k
    fin_cases k <;> rfl
  have hv₂ : (fun k => (v k).2) = vec2 (I := J) (x := x.2) (v 0).2 (v 1).2 := by
    ext k
    fin_cases k <;> rfl
  rw [hv₁, hv₂, hv]
  simp only [metricRicciAt_apply_eq_ricciTensor, ricciTensor_productMetric, vec2, ↓reduceIte]
  rfl

private theorem rm04_continuousOn_prod_of_isSolutionOn
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : SolutionOn (I := J) (M := N) D) (hT : IsSolutionOn T) :
    tensor0SFamilyContinuousOnSet 4 D.carrier
      (fun t x => metricRm04At ((S.family.metric t).prod (T.family.metric t)) x) := by
  have h₁ := tensor0SFamilyContinuousOnSet.pullback_of_contMDiff (I := I.prod J) (J := I)
    (fun t x => S.base.rm04 t x) hS.rm04Cont (Prod.fst : M × N → M) contMDiff_fst
  have h₂ := tensor0SFamilyContinuousOnSet.pullback_of_contMDiff (I := I.prod J) (J := J)
    (fun t x => T.base.rm04 t x) hT.rm04Cont (Prod.snd : M × N → N) contMDiff_snd
  apply (h₁.add h₂).congr
  intro t ht x
  apply ContinuousMultilinearMap.ext
  intro v
  simp only [mfderiv_fst, mfderiv_snd]
  exact (metricRm04At_productMetric_apply (S.family.metric t) (T.family.metric t) x v).symm

theorem isSolutionOn_prod
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : SolutionOn (I := J) (M := N) D) (hT : IsSolutionOn T) :
    IsSolutionOn (S.prod T) := by
  let _ : CompleteSpace (E × F) := FiniteDimensional.complete ℝ (E × F)
  apply isSolutionOn_of_reg
  · exact hS.smoothMetric.prod hT.smoothMetric
  · intro t ht x v w
    exact (metric_hasDerivWithinAt_prod_of_isSolutionOn S hS T hT ht x v w).hasDerivAt
      (D.regular_mem_nhds ht)
  · exact scalar_continuousOn_prod_of_isSolutionOn S hS T hT
  · intro t ht x
    exact scalar_differentiableWithinAt_prod_of_isSolutionOn S hS T hT ht x
  · exact ricci_continuousOn_prod_of_isSolutionOn S hS T hT
  · exact rm04_continuousOn_prod_of_isSolutionOn S hS T hT

end DifferentialGeometry.PDE.RicciFlow
