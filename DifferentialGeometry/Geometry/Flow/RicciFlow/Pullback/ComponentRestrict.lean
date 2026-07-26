import DifferentialGeometry.Geometry.Exponential.LocalAddition
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.SolutionRestrictOpen
import DifferentialGeometry.Geometry.Geodesic.OpenSubtype

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Restricting endpoint-style Ricci-flow data to a connected component

The public forward-uniqueness endpoint is stated on a compact manifold which
need not be connected.  Its hypotheses are deliberately raw: joint chart-Gram
smoothness on the open slab, joint continuity up to the closed initial edge,
and the coefficientwise Ricci-flow equation.  This file transports those exact
hypotheses to the open connected component of an arbitrary point.

The transport does not package the family as an `IsSolutionOn`.  That would
ask for stronger closed-edge smoothness than the endpoint supplies.  Instead,
the chart-Gram fields are pulled back along the smooth open inclusion
`(t,u) ↦ (t, (u : M))`, and the PDE uses the germ-locality theorem
`ricciTensor_restrictOpen`.

No connectedness instance is installed on the ambient manifold.

## Main declarations

* `compRestrict` is the time-dependent metric restricted to one component.
* `compRestrict_init` transports equality of the initial metrics.
* `compRestrict_smooth` transports open-slab joint chart-Gram smoothness.
* `compRestrict_cont` transports closed-edge joint chart-Gram continuity.
* `compRestrict_pde` transports the Ricci-flow equation.
-/

noncomputable section

open Bundle Manifold Set TopologicalSpace
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- A metric family restricted to the open connected component of `p`. -/
noncomputable def compRestrict
    (g : ℝ → SmoothRiemannianMetric I M) (p : M) :
    ℝ → SmoothRiemannianMetric I (connCompOpen (I := I) p) := by
  letI : CompactSpace (connCompOpen (I := I) p) := connCompCompact (I := I) p
  exact fun t => (g t).restrictOpen (I := I) (connCompOpen (I := I) p)

private theorem compBase_mem
    (p : M) (x₀ y : connCompOpen (I := I) p)
    (hy : y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    (y : M) ∈ (trivializationAt E (TangentSpace I) (x₀ : M)).baseSet := by
  rw [trivializationAt_baseSet_eq_chartAt_source] at hy ⊢
  simpa only [TopologicalSpace.Opens.chartAt_eq,
    OpenPartialHomeomorph.subtypeRestr_source] using hy

/-- Equality of two initial metrics survives restriction to a connected component. -/
theorem compRestrict_init
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) (p : M) (a : ℝ)
    (h₀ : g₁ a = g₂ a) :
    compRestrict (I := I) g₁ p a = compRestrict (I := I) g₂ p a := by
  letI : CompactSpace (connCompOpen (I := I) p) := connCompCompact (I := I) p
  simpa only [compRestrict] using congrArg
    (fun g : SmoothRiemannianMetric I M =>
      g.restrictOpen (I := I) (connCompOpen (I := I) p)) h₀

/-- Open-slab joint chart-Gram smoothness survives restriction to a connected component. -/
theorem compRestrict_smooth
    (g : ℝ → SmoothRiemannianMetric I M) (p : M) {a b : ℝ}
    (hsmooth : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun q : ℝ × M => chartGramMatrix (I := I) (g q.1) x₀ q.2 i j)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ∀ (x₀ : connCompOpen (I := I) p) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun q : ℝ × connCompOpen (I := I) p =>
          chartGramMatrix (I := I) (compRestrict (I := I) g p q.1) x₀ q.2 i j)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
  letI : CompactSpace (connCompOpen (I := I) p) := connCompCompact (I := I) p
  intro x₀ i j
  let ρ : ℝ × connCompOpen (I := I) p → ℝ × M := fun q => (q.1, (q.2 : M))
  have hρ : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞ ρ :=
    contMDiff_fst.prodMk
      ((contMDiff_subtype_val (I := I) (U := connCompOpen (I := I) p)).comp contMDiff_snd)
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
  -- `hcomp` is the ambient Gram field after precomposition, whereas
  -- `chartGram_open` is stated `restricted = ambient`; hence `.symm`.
  simpa only [Function.comp_apply, ρ, compRestrict] using
    (chartGram_open (I := I) (g q.1) (connCompOpen (I := I) p) x₀ q.2
      hsource i j).symm

/-- Closed-edge joint chart-Gram continuity survives restriction to a connected component. -/
theorem compRestrict_cont
    (g : ℝ → SmoothRiemannianMetric I M) (p : M) {a b : ℝ}
    (hcont : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun q : ℝ × M => chartGramMatrix (I := I) (g q.1) x₀ q.2 i j)
        (Set.Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ∀ (x₀ : connCompOpen (I := I) p) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun q : ℝ × connCompOpen (I := I) p =>
          chartGramMatrix (I := I) (compRestrict (I := I) g p q.1) x₀ q.2 i j)
        (Set.Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
  letI : CompactSpace (connCompOpen (I := I) p) := connCompCompact (I := I) p
  intro x₀ i j
  let ρ : ℝ × connCompOpen (I := I) p → ℝ × M := fun q => (q.1, (q.2 : M))
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
  -- As above, the congruence needs `ambient = restricted`.
  simpa only [Function.comp_apply, ρ, compRestrict] using
    (chartGram_open (I := I) (g q.1) (connCompOpen (I := I) p) x₀ q.2
      hsource i j).symm

/-- The coefficientwise Ricci-flow PDE survives restriction to a connected component. -/
theorem compRestrict_pde
    (g : ℝ → SmoothRiemannianMetric I M) (p : M) {a b : ℝ}
    (hpde : ∀ t ∈ Set.Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : ℝ => (g s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g t) x v w) (Set.Ici a) t) :
    ∀ t ∈ Set.Ico a b, ∀ (x : connCompOpen (I := I) p) (v w : TangentSpace I x),
      HasDerivWithinAt
        (fun s : ℝ => (compRestrict (I := I) g p s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (M := connCompOpen (I := I) p)
          (compRestrict (I := I) g p t) x v w)
        (Set.Ici a) t := by
  letI : CompactSpace (connCompOpen (I := I) p) := connCompCompact (I := I) p
  intro t ht x v w
  -- For an open subtype these two tangent fibers are definitionally the same
  -- model space `E`; this is also the shared-slot convention of
  -- `ricciTensor_restrictOpen`, so no tangent-map transport is needed.
  simpa only [compRestrict, SmoothRiemannianMetric.restrictOpen_inner,
    ricciTensor_restrictOpen] using hpde t ht (x : M) v w

/-! ## Reassembling componentwise uniqueness -/

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

/-- Equality of two metrics on every connected-component restriction implies
equality of the ambient metrics.  It is enough at `x` to inspect the component
anchored at `x` and evaluate the restricted equality at `connCompPt x`. -/
theorem eq_of_compRestrict
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) (t : ℝ)
    (hcomp : ∀ p : M,
      compRestrict (I := I) g₁ p t = compRestrict (I := I) g₂ p t) :
    g₁ t = g₂ t := by
  apply metric_ext (I := I)
  intro x v w
  have hx := congrArg
    (fun k : SmoothRiemannianMetric I (connCompOpen (I := I) x) =>
      k.inner (connCompPt (I := I) x) v w)
    (hcomp x)
  simpa only [compRestrict, SmoothRiemannianMetric.restrictOpen_inner,
    connCompPt] using hx

/-- Reduction of the raw forward-uniqueness endpoint to the connected case.

The final hypothesis is precisely a connected-manifold uniqueness consumer:
for each component it receives the transported open-slab smoothness,
closed-edge continuity, Ricci-flow PDE, and initial equality, and returns
equality of the restricted flows.  The proof installs no connectedness on the
ambient manifold; a caller proving that hypothesis may locally install
`connCompConnected p` and `connCompCompact p` before invoking the connected
DeTurck/HMF uniqueness theorem. -/
theorem forward_of_comp
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) {a b : ℝ} (hab : a < b)
    (h1smooth : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun q : ℝ × M => chartGramMatrix (I := I) (g₁ q.1) x₀ q.2 i j)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (h1cont : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun q : ℝ × M => chartGramMatrix (I := I) (g₁ q.1) x₀ q.2 i j)
        (Set.Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (h2smooth : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun q : ℝ × M => chartGramMatrix (I := I) (g₂ q.1) x₀ q.2 i j)
        (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (h2cont : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun q : ℝ × M => chartGramMatrix (I := I) (g₂ q.1) x₀ q.2 i j)
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
      (∀ (x₀ : connCompOpen (I := I) p)
          (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
          (fun q : ℝ × connCompOpen (I := I) p =>
            chartGramMatrix (I := I)
              (compRestrict (I := I) g₁ p q.1) x₀ q.2 i j)
          (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) →
      (∀ (x₀ : connCompOpen (I := I) p)
          (i j : Fin (Module.finrank ℝ E)),
        ContinuousOn
          (fun q : ℝ × connCompOpen (I := I) p =>
            chartGramMatrix (I := I)
              (compRestrict (I := I) g₁ p q.1) x₀ q.2 i j)
          (Set.Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) →
      (∀ (x₀ : connCompOpen (I := I) p)
          (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
          (fun q : ℝ × connCompOpen (I := I) p =>
            chartGramMatrix (I := I)
              (compRestrict (I := I) g₂ p q.1) x₀ q.2 i j)
          (Set.Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) →
      (∀ (x₀ : connCompOpen (I := I) p)
          (i j : Fin (Module.finrank ℝ E)),
        ContinuousOn
          (fun q : ℝ × connCompOpen (I := I) p =>
            chartGramMatrix (I := I)
              (compRestrict (I := I) g₂ p q.1) x₀ q.2 i j)
          (Set.Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) →
      (∀ t ∈ Set.Ico a b,
        ∀ (x : connCompOpen (I := I) p) (v w : TangentSpace I x),
          HasDerivWithinAt
            (fun s : ℝ => (compRestrict (I := I) g₁ p s).inner x v w)
            ((-2 : ℝ) * ricciTensor (I := I)
              (compRestrict (I := I) g₁ p t) x v w)
            (Set.Ici a) t) →
      (∀ t ∈ Set.Ico a b,
        ∀ (x : connCompOpen (I := I) p) (v w : TangentSpace I x),
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
    (compRestrict_init (I := I) g₁ g₂ p a h₀) t ht

end DifferentialGeometry.PDE.RicciFlow
