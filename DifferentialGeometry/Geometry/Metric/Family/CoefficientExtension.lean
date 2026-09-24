import DifferentialGeometry.Geometry.Metric.Family.JointSmoothness
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.BorelHalfLine.Parametric

noncomputable section
open Bundle Set Filter Manifold
open DifferentialGeometry DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology BigOperators

namespace DifferentialGeometry.Geometry.Metric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)

omit [I.Boundaryless] [T2Space M] in
private theorem inner_eq_chartGram_sum
    (g : SmoothRiemannianMetric I M) (p y : M) (v w : E) :
    g.inner y ((trivializationAt E (TangentSpace I) p).symmL ℝ y v)
      ((trivializationAt E (TangentSpace I) p).symmL ℝ y w) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr v i * (chartModelBasis E).repr w j *
          chartGramMatrix g p y i j := by
  classical
  let b := chartModelBasis E
  let e := trivializationAt E (TangentSpace I) p
  have hv : e.symmL ℝ y v = ∑ i, b.repr v i • chartBasisVecFiber (I := I) p i y := by
    conv_lhs => rw [← b.sum_repr v]
    simp only [map_sum, map_smul]
    rfl
  have hw : e.symmL ℝ y w = ∑ i, b.repr w i • chartBasisVecFiber (I := I) p i y := by
    conv_lhs => rw [← b.sum_repr w]
    simp only [map_sum, map_smul]
    rfl
  rw [hv, hw]
  have hL : g.inner y (∑ i, b.repr v i • chartBasisVecFiber (I := I) p i y) =
      ∑ i, b.repr v i • g.inner y (chartBasisVecFiber (I := I) p i y) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
  rw [hL, sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [smul_apply, smul_eq_mul, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, smul_eq_mul, chartGramMatrix_apply]
  ring

omit [T2Space M] in
theorem exists_local_metric_coefficient_extension
    (g : ℝ → SmoothRiemannianMetric I M) {a b : ℝ} (hab : a < b)
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => (⟨q.2, (g q.1).inner q.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Icc a b ×ˢ univ)) (p : M) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
      U ⊆ (trivializationAt E (TangentSpace I) p).baseSet ∧
      ∃ A : ℝ × M → E → E → ℝ,
        (∀ v w, ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
          (fun q => A q v w) (univ ×ˢ U)) ∧
        ∀ t ∈ Icc a b, ∀ y ∈ U, ∀ v w,
          A (t, y) v w = (g t).inner y
            ((trivializationAt E (TangentSpace I) p).symmL ℝ y v)
            ((trivializationAt E (TangentSpace I) p).symmL ℝ y w) := by
  classical
  let c : OpenPartialHomeomorph M E :=
    { toPartialEquiv := extChartAt I p
      open_source := isOpen_extChartAt_source p
      open_target := isOpen_extChartAt_target p
      continuousOn_toFun := continuousOn_extChartAt p
      continuousOn_invFun := continuousOn_extChartAt_symm p }
  let F := fun t y i j => chartGramOnE (I := I) (g (a + t)) p i j y
  have hF : ContDiffOn ℝ ∞ (Function.uncurry F) (Icc 0 (b - a) ×ˢ c.target) := by
    apply contDiffOn_pi.mpr
    intro i
    apply contDiffOn_pi.mpr
    intro j
    exact (chartGramOnE_joint_contDiffOn g (Icc a b) hg p i j).comp
      ((contDiff_const.add contDiff_fst).prodMk contDiff_snd).contDiffOn
      (fun q hq => ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, hq.2⟩)
  have hp : p ∈ c.source := mem_extChartAt_source p
  obtain ⟨Fext, W₀, hW₀, hFext, hEq⟩ :=
    DifferentialGeometry.Analysis.borel_interval_extend_param F (b - a) (sub_pos.mpr hab)
      c.target (c p) (by rw [c.open_target.interior_eq]; exact c.map_source hp) hF
  obtain ⟨W, hWW₀, hW, hpW⟩ := mem_nhds_iff.mp hW₀
  let U : Set M := c.source ∩ c ⁻¹' W
  have hU : IsOpen U := c.isOpen_inter_preimage hW
  have hUb : U ⊆ (trivializationAt E (TangentSpace I) p).baseSet := by
    intro y hy
    simpa only [TangentBundle.trivializationAt_baseSet, c, extChartAt_source] using hy.1
  let A := fun q : ℝ × M => fun v w : E =>
    ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      (chartModelBasis E).repr v i * (chartModelBasis E).repr w j * Fext (q.1 - a) (c q.2) i j
  refine ⟨U, hU, ⟨hp, hpW⟩, hUb, A, ?_, ?_⟩
  · intro v w
    have hct : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) ∞
        (fun q : ℝ × M => c q.2) (univ ×ˢ U) :=
      (contMDiffOn_extChartAt (I := I) (x := p)).comp contMDiffOn_snd
        (fun q hq => by simpa only [c, extChartAt_source, Set.mem_preimage] using hq.2.1)
    have hmap : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ × E) ∞
        (fun q : ℝ × M => (q.1 - a, c q.2)) (univ ×ˢ U) :=
      (contMDiff_fst.sub contMDiff_const).contMDiffOn.prodMk_space hct
    have hex := hFext.contMDiffOn.comp hmap (fun q hq => ⟨mem_univ _, hWW₀ hq.2.2⟩)
    intro q hq
    apply ContMDiffWithinAt.sum
    intro i _
    apply ContMDiffWithinAt.sum
    intro j _
    exact contMDiffWithinAt_const.mul ((contMDiffWithinAt_pi_space.mp
      (contMDiffWithinAt_pi_space.mp (hex q hq) i)) j)
  · intro t ht y hy v w
    have htime : t - a ∈ Icc 0 (b - a) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have he := hEq (t - a) htime (c y) (hWW₀ hy.2)
    dsimp [A]
    rw [he]
    change ∑ i, ∑ j, _ * chartGramOnE (g (a + (t - a))) p i j (c y) = _
    rw [show a + (t - a) = t by ring]
    have hc : c.symm (c y) = y := c.left_inv hy.1
    change (∑ i, ∑ j, _ * chartGramMatrix (g t) p (c.symm (c y)) i j) = _
    rw [hc]
    exact (inner_eq_chartGram_sum (g t) p y v w).symm

end DifferentialGeometry.Geometry.Metric
