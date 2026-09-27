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

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
  [CompactSpace M] [Nonempty M] [I.Boundaryless] in
theorem ProductCurve.not_isRampOn_zero (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) : ¬ c.IsRampOn g 0 {a} := by
  rintro ⟨-, hangle⟩
  have hzero : c.angle g 0 0 a = 0 := by
    simp [ProductCurve.angle, ProductCurve.inner, ProductCurve.unitTangent,
      ProductCurve.verticalUnit]
  have hpos := hangle 0 a (mem_singleton a)
  rw [hzero] at hpos
  exact lt_irrefl 0 hpos

theorem nonempty_rampFamilyInput_of_forall_not_isRampOn
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ) {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (h : ∀ c : ProductCurve M, ¬ (c.SmoothOn (I := I) {a} ∧
      c.IsRampOn B.family.metric lambda {a})) :
    Nonempty (RampFamilyInput (I := I) (M := M) (D := D) (a := a) (b := b) (N := N)
      B lambda e) :=
  ⟨⟨fun c₀ hs₀ hr₀ => absurd ⟨hs₀, hr₀⟩ (h c₀)⟩⟩

theorem nonempty_rampFamilyInput_zero_lambda
    (B : RicciBackground (I := I) (M := M) D a b) {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N) :
    Nonempty (RampFamilyInput (I := I) (M := M) (D := D) (a := a) (b := b) (N := N)
      B 0 e) :=
  nonempty_rampFamilyInput_of_forall_not_isRampOn B 0 e fun c =>
    fun h => ProductCurve.not_isRampOn_zero c B.family.metric h.2

private def verticalRamp (p : M) : ProductCurve M where
  map z _ := (p, z)
  y x _ := x
  degree := 1
  lift_eq _ _ := rfl
  increment _ _ := by simp

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [T2Space M] [CompactSpace M] [Nonempty M] [I.Boundaryless] in
private theorem verticalRamp_smoothOn (p : M) (a : ℝ) :
    (verticalRamp p).SmoothOn (I := I) {a} := by
  refine ⟨?_, ?_⟩
  · have h : (fun q : ℝ × ℝ => (verticalRamp p).projection.lift q.1 q.2) = fun _ => p := by
      funext q
      rfl
    simp only [CurveMap.SmoothOn]
    rw [h]
    exact contMDiffOn_const
  · have h : (fun q : ℝ × ℝ => (verticalRamp p).y q.1 q.2) = fun q : ℝ × ℝ => q.1 := by
      funext q
      rfl
    rw [h]
    exact contDiff_fst.contDiffOn

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
  [CompactSpace M] [Nonempty M] [I.Boundaryless] in
private theorem verticalRamp_isRampOn (p : M) (g : ℝ → SmoothRiemannianMetric I M)
    (a lambda : ℝ) (hlambda : 0 < lambda) :
    (verticalRamp p).IsRampOn g lambda {a} := by
  refine ⟨?_, ?_⟩
  · intro x t _ hx
    have hzero : ((verticalRamp p).X (I := I) x t).2 = 0 := by rw [hx]; rfl
    have hone : ((verticalRamp p).X (I := I) x t).2 = 1 := by
      simp [ProductCurve.X, verticalRamp]
    rw [hone] at hzero
    exact one_ne_zero hzero
  · intro x t ht
    rw [mem_singleton_iff] at ht
    rw [ht]
    have hX2 : ((verticalRamp p).X (I := I) x a).2 = 1 := by
      simp [ProductCurve.X, verticalRamp]
    have hspeed : (verticalRamp p).speed g lambda x a =
        Real.sqrt ((g a).inner ((verticalRamp p).projection.lift x a)
          ((verticalRamp p).X (I := I) x a).1
          ((verticalRamp p).X (I := I) x a).1 + lambda ^ 2) := by
      rw [ProductCurve.speed, ProductCurve.inner, hX2]
      ring_nf
    have hspeed_pos : 0 < (verticalRamp p).speed g lambda x a := by
      rw [hspeed]
      refine Real.sqrt_pos.mpr ?_
      have hnn : 0 ≤ (g a).inner ((verticalRamp p).projection.lift x a)
          ((verticalRamp p).X (I := I) x a).1 ((verticalRamp p).X (I := I) x a).1 := by
        rcases eq_or_ne ((verticalRamp p).X (I := I) x a).1 0 with h | h
        · simp only [h, map_zero]
          rfl
        · exact ((g a).pos _ _ h).le
      nlinarith [sq_pos_of_ne_zero (ne_of_gt hlambda), hnn]
    have hangle : (verticalRamp p).angle g lambda x a =
        lambda ^ 2 * ((verticalRamp p).speed g lambda x a)⁻¹ * lambda⁻¹ := by
      rw [ProductCurve.angle, ProductCurve.inner, ProductCurve.unitTangent,
        ProductCurve.verticalUnit]
      simp only [Prod.smul_fst, Prod.smul_snd, map_zero, zero_add, hX2]
      ring
    rw [hangle]
    positivity

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
  [CompactSpace M] [Nonempty M] [I.Boundaryless] in
theorem exists_smoothOn_and_isRampOn (p : M) (g : ℝ → SmoothRiemannianMetric I M)
    (a lambda : ℝ) (hlambda : 0 < lambda) :
    ∃ c : ProductCurve M, c.SmoothOn (I := I) {a} ∧ c.IsRampOn g lambda {a} :=
  ⟨verticalRamp p, verticalRamp_smoothOn p a, verticalRamp_isRampOn p g a lambda hlambda⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
