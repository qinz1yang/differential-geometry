import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SlimFibreGraphApplications

/-!
# LFR20 step 4 on an exact splitting: the zero fibre is homeomorphic to the factor

`nonempty_homeomorph_zeroLevel_of_splitting`: let `N` be a complete finite-order Riemannian manifold
with an exact splitting `Φ : N ≃ᵢ ℓ²(ℝ × W)`, `W` compact, and LFR18's vertical field `V`. Let
`J : N → X` (the comparison embedding `j_i`) be continuous and injective on the cylinder
`C = {|t| ≤ b}`, and `η : X → ℝ` continuous with, on `C`: `η ∘ J` differentiable,
`d(η ∘ J)(V) > 0` (LFR20.1), `|η ∘ J - t| < c ≤ b`. If the cylinder's interior zeros lie in `S` and
every zero of `η` in `S` is `J` of a cylinder point (LFR20.2 + LFR14's coverage), then
`{y ∈ S | η y = 0}` is homeomorphic to the zero factor `{x ∈ N | t(x) = 0}`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Metric Bundle WithLp
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [RiemannianBundle (fun x : N => TangentSpace I x)] [IsRiemannianManifold I N]
  [CompleteSpace N] {r : ℕ∞} {W : Type*} [MetricSpace W]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [IsManifold I ∞ N] [RiemannianBundle (fun x : N => TangentSpace I x)]
  [IsRiemannianManifold I N] [CompleteSpace N] in
/-- The zero factor of an exact splitting with compact factor is compact. -/
theorem isCompact_splitting_zeroFactor [CompactSpace W] (Φ : N ≃ᵢ WithLp 2 (ℝ × W)) :
    IsCompact {x : N | (Φ x).fst = 0} := by
  have hc : Continuous fun w : W => Φ.symm (toLp 2 ((0 : ℝ), w)) :=
    Φ.symm.continuous.comp ((WithLp.prod_continuous_toLp 2 ℝ W).comp
      (continuous_const.prodMk continuous_id))
  have heq : {x : N | (Φ x).fst = 0} = range fun w : W => Φ.symm (toLp 2 ((0 : ℝ), w)) := by
    ext x
    constructor
    · intro hx
      refine ⟨(Φ x).snd, ?_⟩
      apply Φ.injective
      rw [Φ.apply_symm_apply]
      change toLp 2 ((0 : ℝ), (Φ x).snd) = toLp 2 ((Φ x).fst, (Φ x).snd)
      rw [show (Φ x).fst = 0 from hx]
    · rintro ⟨w, rfl⟩
      change (Φ (Φ.symm (toLp 2 ((0 : ℝ), w)))).fst = 0
      rw [Φ.apply_symm_apply]
      rfl
  rw [heq]
  exact isCompact_range hc

/-- **LFR20 step 4 on an exact splitting.** The zero level of `η` in `S` is homeomorphic to the
zero factor of `N`. -/
theorem nonempty_homeomorph_zeroLevel_of_splitting [CompactSpace W]
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : N) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (Φ : N ≃ᵢ WithLp 2 (ℝ × W)) {ℓ : ℝ} (hℓ : 0 < ℓ) (V : ∀ x : N, TangentSpace I x)
    (hVdir : ∀ x, G.finiteMinimizingDirectionsTo
      {Φ.symm (toLp 2 ((Φ x).fst + ℓ, (Φ x).snd))} x = {V x})
    {X : Type*} [TopologicalSpace X] [T2Space X] (J : N → X) {b c : ℝ} (hc : 0 < c)
    (hcb : c ≤ b) (hJ : ContinuousOn J {x | |(Φ x).fst| ≤ b})
    (hJinj : InjOn J {x | |(Φ x).fst| ≤ b}) {η : X → ℝ} (hη : Continuous η)
    (hfd : ∀ x, |(Φ x).fst| ≤ b → MDifferentiableAt I 𝓘(ℝ, ℝ) (η ∘ J) x)
    (hpos : ∀ x, |(Φ x).fst| ≤ b → 0 < mvfderiv I (η ∘ J) x (V x))
    (hval : ∀ x, |(Φ x).fst| ≤ b → |η (J x) - (Φ x).fst| < c)
    {S : Set X} (hS : ∀ x, |(Φ x).fst| < b → η (J x) = 0 → J x ∈ S)
    (hencl : ∀ y ∈ S, η y = 0 → ∃ x, |(Φ x).fst| ≤ b ∧ J x = y) :
    Nonempty ({y // y ∈ S ∧ η y = 0} ≃ₜ {x : N // (Φ x).fst = 0}) := by
  have : CompactSpace {x : N // (Φ x).fst = 0} :=
    isCompact_iff_compactSpace.mp (isCompact_splitting_zeroFactor Φ)
  have hfstL : ∀ (t : ℝ) (w : W), (Φ (Φ.symm (toLp 2 (t, w)))).fst = t := by
    intro t w
    rw [Φ.apply_symm_apply]
    rfl
  have hsndL : ∀ (t : ℝ) (w : W), (Φ (Φ.symm (toLp 2 (t, w)))).snd = w := by
    intro t w
    rw [Φ.apply_symm_apply]
    rfl
  let L : ℝ × {x : N // (Φ x).fst = 0} → N := fun q => Φ.symm (toLp 2 (q.1, (Φ q.2.1).snd))
  have hLc : Continuous L :=
    Φ.symm.continuous.comp ((WithLp.prod_continuous_toLp 2 ℝ W).comp
      (continuous_fst.prodMk ((WithLp.prod_continuous_ofLp 2 ℝ W).snd.comp
        (Φ.continuous.comp (continuous_subtype_val.comp continuous_snd)))))
  have hLmaps : MapsTo L (Icc (-b) b ×ˢ univ) {x | |(Φ x).fst| ≤ b} := by
    rintro ⟨t, z⟩ ⟨ht, -⟩
    change |(Φ (Φ.symm (toLp 2 (t, (Φ z.1).snd)))).fst| ≤ b
    rw [hfstL]
    exact abs_le.mpr ht
  let P : ℝ × {x : N // (Φ x).fst = 0} → X := J ∘ L
  have hP : ContinuousOn P (Icc (-b) b ×ˢ univ) := hJ.comp hLc.continuousOn hLmaps
  have hzeq : ∀ z : {x : N // (Φ x).fst = 0}, Φ z.1 = toLp 2 ((0 : ℝ), (Φ z.1).snd) := by
    intro z
    change toLp 2 ((Φ z.1).fst, (Φ z.1).snd) = toLp 2 ((0 : ℝ), (Φ z.1).snd)
    exact congrArg (fun a => toLp 2 (a, (Φ z.1).snd)) z.2
  have hPinj : InjOn P (Icc (-b) b ×ˢ univ) := by
    rintro ⟨t, z⟩ hq ⟨t', z'⟩ hq' h
    have h1 := hJinj (hLmaps hq) (hLmaps hq') h
    have h2 := congrArg Φ h1
    simp only [L, Φ.apply_symm_apply] at h2
    have h3 : (t, (Φ z.1).snd) = (t', (Φ z'.1).snd) := congrArg WithLp.ofLp h2
    simp only [Prod.mk.injEq] at h3
    refine Prod.ext h3.1 (Subtype.ext (Φ.injective ?_))
    rw [hzeq z, hzeq z', h3.2]
  have hmono : ∀ z : {x : N // (Φ x).fst = 0},
      StrictMonoOn (fun t => η (P (t, z))) (Icc (-b) b) := by
    intro z
    refine strictMonoOn_comp_splitting_line G hr hnorm Φ hℓ V hVdir (f := η ∘ J) (Φ z.1).snd
      (fun s hs => hfd _ ?_) (fun s hs => hpos _ ?_)
    · rw [hfstL]; exact abs_le.mpr hs
    · rw [hfstL]; exact abs_le.mpr hs
  have hval' : ∀ t ∈ Icc (-b) b, ∀ z, |η (P (t, z)) - t| < c := by
    intro t ht z
    have h := hval (L (t, z)) (hLmaps ⟨ht, mem_univ _⟩)
    simp only [L, hfstL] at h
    exact h
  have hS' : ∀ t ∈ Ioo (-b) b, ∀ z, η (P (t, z)) = 0 → P (t, z) ∈ S := by
    intro t ht z h0
    refine hS (L (t, z)) ?_ h0
    simp only [L, hfstL]
    exact abs_lt.mpr ht
  have hencl' : ∀ y ∈ S, η y = 0 → ∃ t ∈ Icc (-b) b, ∃ z, P (t, z) = y := by
    intro y hy hy0
    obtain ⟨x, hx, rfl⟩ := hencl y hy hy0
    refine ⟨(Φ x).fst, abs_le.mp hx, ⟨Φ.symm (toLp 2 ((0 : ℝ), (Φ x).snd)), hfstL _ _⟩, ?_⟩
    change J (Φ.symm (toLp 2 ((Φ x).fst, (Φ (Φ.symm (toLp 2 ((0 : ℝ), (Φ x).snd)))).snd))) = J x
    rw [hsndL]
    congr 1
    apply Φ.injective
    rw [Φ.apply_symm_apply]
    rfl
  exact nonempty_homeomorph_zeroLevel_of_graph hP hPinj hη hmono hval' hc hcb hS' hencl'

end DifferentialGeometry.Geometry.Collapse
