import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.BoundaryIsotopy

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [hBoundary : I.Boundaryless] [hT2 : T2Space M] [hCompact : CompactSpace M]
  [hNonempty : Nonempty M] [SigmaCompactSpace M]
  {a b : ℝ}

namespace CurveMap

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] hBoundary hT2 hCompact
  hNonempty [SigmaCompactSpace M] in
theorem smoothOn_mono {c : CurveMap M} {J J' : Set ℝ} (h : c.SmoothOn (I := I) J)
    (hsub : J' ⊆ J) : c.SmoothOn (I := I) J' :=
  h.mono fun _ hp => ⟨hp.1, hsub hp.2⟩

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] hBoundary hT2 hCompact
  hNonempty [SigmaCompactSpace M] in
theorem immersedOn_mono {c : CurveMap M} {J J' : Set ℝ} (h : c.ImmersedOn (I := I) J)
    (hsub : J' ⊆ J) : c.ImmersedOn (I := I) J' :=
  fun x t ht => h x t (hsub ht)

end CurveMap

omit [FiniteDimensional ℝ E] [CompleteSpace E] hBoundary hT2 hCompact hNonempty
  [SigmaCompactSpace M] in
def HasBoundaryIsotopyVelocityExtension (a b : ℝ) : Prop :=
  ∀ γ : ℝ → ContinuousFreeLoop M,
    (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b) →
    (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b) →
    (∀ t ∈ Icc a b, Topology.IsEmbedding (γ t)) →
    LoopFamilyVelocityExtension (I := I) a b γ

omit [CompleteSpace E] hNonempty in
theorem rfs_csf_boundary_isotopy_of_hasBoundaryIsotopyVelocityExtension
    (hfront : HasBoundaryIsotopyVelocityExtension (I := I) (M := M) a b)
    (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b))
    (hemb : ∀ t ∈ Icc a b, Topology.IsEmbedding (γ t))
    (t₀ : ℝ) (ht₀ : t₀ ∈ Icc a b) (hab : a < b) :
    ∃ ε > 0, ∃ Φ : ℝ → Diffeomorph I I M M ∞,
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun p : M × ℝ => Φ p.2 p.1)
        (univ ×ˢ (Icc a b ∩ Ioo (t₀ - ε) (t₀ + ε))) ∧
      (∀ p, Φ t₀ p = p) ∧
      ∀ t ∈ Icc a b ∩ Ioo (t₀ - ε) (t₀ + ε), ∀ z, Φ t (γ t₀ z) = γ t z := by
  let _ := hab
  exact rfs_csf_boundary_isotopy_of_velocityExtension a b γ t₀ ht₀
    (hfront γ hγ hi hemb)

omit [CompleteSpace E] hNonempty in
theorem rfs_csf_boundary_isotopy_of_hasBoundaryIsotopyVelocityExtension_subset
    {α β : ℝ} (hfront : HasBoundaryIsotopyVelocityExtension (I := I) (M := M) a b)
    (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc α β))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc α β))
    (hemb : ∀ t ∈ Icc α β, Topology.IsEmbedding (γ t))
    (ha : α ≤ a) (hb : b ≤ β)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Icc a b) (hab : a < b) :
    ∃ ε > 0, ∃ Φ : ℝ → Diffeomorph I I M M ∞,
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun p : M × ℝ => Φ p.2 p.1)
        (univ ×ˢ (Icc a b ∩ Ioo (t₀ - ε) (t₀ + ε))) ∧
      (∀ p, Φ t₀ p = p) ∧
      ∀ t ∈ Icc a b ∩ Ioo (t₀ - ε) (t₀ + ε), ∀ z, Φ t (γ t₀ z) = γ t z :=
  rfs_csf_boundary_isotopy_of_hasBoundaryIsotopyVelocityExtension (I := I) (M := M)
    hfront γ (CurveMap.smoothOn_mono hγ (Icc_subset_Icc ha hb))
    (CurveMap.immersedOn_mono hi (Icc_subset_Icc ha hb))
    (fun t ht => hemb t (Icc_subset_Icc ha hb ht)) t₀ ht₀ hab

omit [CompleteSpace E] hNonempty in
theorem rfs_csf_boundary_isotopy_of_constantLoopFamily
    (γ : ℝ → ContinuousFreeLoop M) (hconst : ∀ t t' : ℝ, γ t = γ t')
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b))
    (hemb : ∀ t ∈ Icc a b, Topology.IsEmbedding (γ t))
    (t₀ : ℝ) (ht₀ : t₀ ∈ Icc a b) (hab : a < b) :
    ∃ ε > 0, ∃ Φ : ℝ → Diffeomorph I I M M ∞,
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ (fun p : M × ℝ => Φ p.2 p.1)
        (univ ×ˢ (Icc a b ∩ Ioo (t₀ - ε) (t₀ + ε))) ∧
      (∀ p, Φ t₀ p = p) ∧
      ∀ t ∈ Icc a b ∩ Ioo (t₀ - ε) (t₀ + ε), ∀ z, Φ t (γ t₀ z) = γ t z := by
  let _ := hγ
  let _ := hi
  let _ := hemb
  let _ := hab
  exact rfs_csf_boundary_isotopy_of_velocityExtension a b γ t₀ ht₀
    (loopFamilyVelocityExtension_zero a b γ hconst)

omit [CompleteSpace E] hCompact hNonempty [SigmaCompactSpace M] in
theorem loopFamilyVelocityExtension_of_compactSupportFlow
    (γ₀ : ContinuousFreeLoop M) (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v)) (a b : ℝ) :
    LoopFamilyVelocityExtension (I := I) a b
      (fun t : ℝ =>
        (⟨fun x : M => Diffeomorph.compactSupportFlow v hv hsupp t x,
          (Diffeomorph.contMDiff_compactSupportFlow v hv hsupp).continuous.comp
            (continuous_const.prodMk continuous_id)⟩ : C(M, M)).comp γ₀) := by
  refine ⟨fun _ p => v p, hv.comp contMDiff_snd, ?_, ?_⟩
  · intro t _ z
    exact ((Diffeomorph.isMIntegralCurve_compactSupportFlow v hv hsupp (γ₀ z)) t).hasMFDerivWithinAt
  · intro t _ z
    exact ((Diffeomorph.isMIntegralCurve_compactSupportFlow v hv hsupp (γ₀ z)) t).hasMFDerivWithinAt

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
