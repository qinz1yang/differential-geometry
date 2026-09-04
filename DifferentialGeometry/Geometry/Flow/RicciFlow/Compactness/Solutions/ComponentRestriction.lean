import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.OpenRestriction
import DifferentialGeometry.Geometry.Geodesic.Naturality.OpenSubtype
import DifferentialGeometry.Topology.Manifold.ConnectedComponent


open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set TopologicalSpace
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.Integral.Measure

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

noncomputable def compRestrict
    (g : ℝ → SmoothRiemannianMetric I M) (p : M) :
    ℝ → SmoothRiemannianMetric I (connectedComponentOpen (I := I) p) := by
  letI : CompactSpace (connectedComponentOpen (I := I) p) := connectedComponentOpen_compactSpace (I := I) p
  exact fun t => (g t).restrictOpen (I := I) (connectedComponentOpen (I := I) p)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem compBase_mem
    (p : M) (x₀ y : connectedComponentOpen (I := I) p)
    (hy : y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    (y : M) ∈ (trivializationAt E (TangentSpace I) (x₀ : M)).baseSet := by
  rw [trivializationAt_baseSet_eq_chartAt_source] at hy ⊢
  rw [TopologicalSpace.Opens.chartAt_eq,
    OpenPartialHomeomorph.subtypeRestr_source] at hy
  exact hy

omit [NeZero (Module.finrank ℝ E)]
  [BoundarylessManifold I M]
  [SigmaCompactSpace M] in
theorem compRestrict_initial
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) (p : M) (a : ℝ)
    (h₀ : g₁ a = g₂ a) :
    compRestrict (I := I) g₁ p a = compRestrict (I := I) g₂ p a := by
  let _ := (inferInstance : (CompactSpace M))
  let : CompactSpace (connectedComponentOpen (I := I) p) := connectedComponentOpen_compactSpace (I := I) p
  simpa only [compRestrict] using congrArg
    (fun g : SmoothRiemannianMetric I M =>
      g.restrictOpen (I := I) (connectedComponentOpen (I := I) p)) h₀

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem compRestrict_smooth
    [compactSpace : CompactSpace M]
    (g : ℝ → SmoothRiemannianMetric I M) (p : M) {a b : ℝ}
    (hsmooth : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun q : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g q.1) x₀ q.2 i j)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ∀ (x₀ : connectedComponentOpen (I := I) p) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun q : ℝ × connectedComponentOpen (I := I) p =>
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (compRestrict (I := I) g p q.1) x₀ q.2 i j)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
  let _ := compactSpace
  let : CompactSpace (connectedComponentOpen (I := I) p) := connectedComponentOpen_compactSpace (I := I) p
  intro x₀ i j
  let ρ : ℝ × connectedComponentOpen (I := I) p → ℝ × M := fun q => (q.1, (q.2 : M))
  have hρ : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞ ρ :=
    contMDiff_fst.prodMk
      ((contMDiff_subtype_val (I := I) (U := connectedComponentOpen (I := I) p)).comp contMDiff_snd)
  have hmaps : Set.MapsTo ρ
      (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)
      (Set.Ioo a b ×ˢ
        (trivializationAt E (TangentSpace I) (x₀ : M)).baseSet) := by
    intro q hq
    exact ⟨hq.1, compBase_mem (I := I) p x₀ q.2 hq.2⟩
  have hcomp := (hsmooth (x₀ : M) i j).comp hρ.contMDiffOn hmaps
  refine hcomp.congr (fun q hq => ?_)
  have hsource : (q.2 : M) ∈ (chartAt H (x₀ : M)).source := by
    simpa only [trivializationAt_baseSet_eq_chartAt_source] using
      compBase_mem (I := I) p x₀ q.2 hq.2
  simpa only [Function.comp_apply, ρ, compRestrict] using
    (chartGram_open (I := I) (g q.1) (connectedComponentOpen (I := I) p) x₀ q.2
      hsource i j)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem compRestrict_cont
    [compactSpace : CompactSpace M]
    (g : ℝ → SmoothRiemannianMetric I M) (p : M) {a b : ℝ}
    (hcont : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun q : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g q.1) x₀ q.2 i j)
        (Set.Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ∀ (x₀ : connectedComponentOpen (I := I) p) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun q : ℝ × connectedComponentOpen (I := I) p =>
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (compRestrict (I := I) g p q.1) x₀ q.2 i j)
        (Set.Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
  let _ := compactSpace
  let : CompactSpace (connectedComponentOpen (I := I) p) := connectedComponentOpen_compactSpace (I := I) p
  intro x₀ i j
  let ρ : ℝ × connectedComponentOpen (I := I) p → ℝ × M := fun q => (q.1, (q.2 : M))
  have hρ : Continuous ρ :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hmaps : Set.MapsTo ρ
      (Set.Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)
      (Set.Ico a b ×ˢ
        (trivializationAt E (TangentSpace I) (x₀ : M)).baseSet) := by
    intro q hq
    exact ⟨hq.1, compBase_mem (I := I) p x₀ q.2 hq.2⟩
  have hcomp := (hcont (x₀ : M) i j).comp hρ.continuousOn hmaps
  refine hcomp.congr (fun q hq => ?_)
  have hsource : (q.2 : M) ∈ (chartAt H (x₀ : M)).source := by
    simpa only [trivializationAt_baseSet_eq_chartAt_source] using
      compBase_mem (I := I) p x₀ q.2 hq.2
  simpa only [Function.comp_apply, ρ, compRestrict] using
    (chartGram_open (I := I) (g q.1) (connectedComponentOpen (I := I) p) x₀ q.2
      hsource i j)

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem compRestrict_pde
    (g : ℝ → SmoothRiemannianMetric I M) (p : M) {a b : ℝ}
    (hpde : ∀ t ∈ Set.Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : ℝ => (g s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g t) x v w) (Set.Ici a) t) :
    ∀ t ∈ Set.Ico a b, ∀ (x : connectedComponentOpen (I := I) p) (v w : TangentSpace I x),
      HasDerivWithinAt
        (fun s : ℝ => (compRestrict (I := I) g p s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (M := connectedComponentOpen (I := I) p)
          (compRestrict (I := I) g p t) x v w)
        (Set.Ici a) t := by
  let : CompactSpace (connectedComponentOpen (I := I) p) := connectedComponentOpen_compactSpace (I := I) p
  intro t ht x v w
  let vM : TangentSpace I (x : M) :=
    mfderiv I I (Subtype.val : connectedComponentOpen (I := I) p → M) x v
  let wM : TangentSpace I (x : M) :=
    mfderiv I I (Subtype.val : connectedComponentOpen (I := I) p → M) x w
  have h := hpde t ht (x : M) vM wM
  convert h using 1
  · funext s
    change ((g s).restrictOpen (I := I) (connectedComponentOpen (I := I) p)).inner x v w =
      (g s).inner (x : M) vM wM
    have hopen := SmoothRiemannianMetric.restrictOpen_inner
      (I := I) (g s) (connectedComponentOpen (I := I) p) x v w
    simpa only [vM, wM, mfderiv_subtype_val_apply] using hopen
  · exact congrArg (fun z : ℝ => (-2 : ℝ) * z)
      (ricciTensor_restrictOpen (I := I) (g t) (connectedComponentOpen (I := I) p) x v w)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem metric_ext
    (g h : SmoothRiemannianMetric I M)
    (hinner : ∀ (x : M) (v w : TangentSpace I x),
      g.inner x v w = h.inner x v w) :
    g = h := by
  obtain ⟨i₁, s₁, p₁, b₁, c₁⟩ := g
  obtain ⟨i₂, s₂, p₂, b₂, c₂⟩ := h
  have hi : i₁ = i₂ :=
    funext fun x => ContinuousLinearMap.ext fun v =>
      ContinuousLinearMap.ext fun w => hinner x v w
  subst hi
  rfl

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [CompactSpace M] in
theorem eq_of_compRestrict
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) (t : ℝ)
    (hcomp : ∀ p : M,
      compRestrict (I := I) g₁ p t = compRestrict (I := I) g₂ p t) :
    g₁ t = g₂ t := by
  apply metric_ext (I := I)
  intro x v w
  have hx := congrArg
    (fun k : SmoothRiemannianMetric I (connectedComponentOpen (I := I) x) =>
      k.inner (connectedComponentPoint (I := I) x) v w)
    (hcomp x)
  change (g₁ t).inner x v w = (g₂ t).inner x v w at hx
  exact hx

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem forward_of_comp
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) {a b : ℝ} (hab : a < b)
    (h1smooth : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun q : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g₁ q.1) x₀ q.2 i j)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (h1cont : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun q : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g₁ q.1) x₀ q.2 i j)
        (Set.Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (h2smooth : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun q : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g₂ q.1) x₀ q.2 i j)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (h2cont : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun q : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g₂ q.1) x₀ q.2 i j)
        (Set.Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (h1pde : ∀ t ∈ Set.Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : ℝ => (g₁ s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g₁ t) x v w) (Set.Ici a) t)
    (h2pde : ∀ t ∈ Set.Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : ℝ => (g₂ s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g₂ t) x v w) (Set.Ici a) t)
    (h₀ : g₁ a = g₂ a)
    (hconnected : ∀ p : M,
      a < b →
      (∀ (x₀ : connectedComponentOpen (I := I) p)
          (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
          (fun q : ℝ × connectedComponentOpen (I := I) p =>
            DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I)
              (compRestrict (I := I) g₁ p q.1) x₀ q.2 i j)
          (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) →
      (∀ (x₀ : connectedComponentOpen (I := I) p)
          (i j : Fin (Module.finrank ℝ E)),
        ContinuousOn
          (fun q : ℝ × connectedComponentOpen (I := I) p =>
            DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I)
              (compRestrict (I := I) g₁ p q.1) x₀ q.2 i j)
          (Set.Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) →
      (∀ (x₀ : connectedComponentOpen (I := I) p)
          (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
          (fun q : ℝ × connectedComponentOpen (I := I) p =>
            DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I)
              (compRestrict (I := I) g₂ p q.1) x₀ q.2 i j)
          (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) →
      (∀ (x₀ : connectedComponentOpen (I := I) p)
          (i j : Fin (Module.finrank ℝ E)),
        ContinuousOn
          (fun q : ℝ × connectedComponentOpen (I := I) p =>
            DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I)
              (compRestrict (I := I) g₂ p q.1) x₀ q.2 i j)
          (Set.Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) →
      (∀ t ∈ Set.Ico a b,
        ∀ (x : connectedComponentOpen (I := I) p) (v w : TangentSpace I x),
          HasDerivWithinAt
            (fun s : ℝ => (compRestrict (I := I) g₁ p s).inner x v w)
            ((-2 : ℝ) * ricciTensor (I := I)
              (compRestrict (I := I) g₁ p t) x v w)
            (Set.Ici a) t) →
      (∀ t ∈ Set.Ico a b,
        ∀ (x : connectedComponentOpen (I := I) p) (v w : TangentSpace I x),
          HasDerivWithinAt
            (fun s : ℝ => (compRestrict (I := I) g₂ p s).inner x v w)
            ((-2 : ℝ) * ricciTensor (I := I)
              (compRestrict (I := I) g₂ p t) x v w)
            (Set.Ici a) t) →
      compRestrict (I := I) g₁ p a = compRestrict (I := I) g₂ p a →
      ∀ t ∈ Set.Ico a b,
        compRestrict (I := I) g₁ p t = compRestrict (I := I) g₂ p t) :
    ∀ t ∈ Set.Ico a b, g₁ t = g₂ t := by
  intro t ht
  apply eq_of_compRestrict (I := I) g₁ g₂ t
  intro p
  exact hconnected p hab
    (compRestrict_smooth (I := I) g₁ p h1smooth)
    (compRestrict_cont (I := I) g₁ p h1cont)
    (compRestrict_smooth (I := I) g₂ p h2smooth)
    (compRestrict_cont (I := I) g₂ p h2cont)
    (compRestrict_pde (I := I) g₁ p h1pde)
    (compRestrict_pde (I := I) g₂ p h2pde)
    (compRestrict_initial (I := I) g₁ g₂ p a h₀) t ht

end DifferentialGeometry.PDE.RicciFlow
