import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SoulCarrierBase
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ClosedGeodesicSlice

/-!
# Consumers of BASE-1b (lane CMS3-CARRIER, group G1)

* `soulBase_of_slice_dim_one`: the one-dimensional base contract for a soul. A compact connected
  one-dimensional totally geodesic `C^r` slice `S` (`r ≥ 2`) has the smooth carrier `AddCircle 1`
  with `b : AddCircle 1 → M` of class `C^{r−1}`, injective, `range b = S`, and a left inverse
  `R : M → AddCircle 1` of class `C^{r−1}` at every point of `S` (BASE-1a of CMS3-SLICE, then
  BASE-1b);
* `soulBase_closedGeodesic_mfderiv_injective`: the base map is an immersion (`dR ∘ db = id`), the
  property that the LFR46 restatement (disposition D1) and EXIT-51 consume.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Metric Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- **The one-dimensional base contract.** A compact connected one-dimensional totally geodesic
`C^r` slice has the circle carrier with a `C^{r−1}` injective base map onto it and a left inverse
that is `C^{r−1}` at every point of the slice. -/
theorem soulBase_of_slice_dim_one
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} (hSc : IsCompact S) (hconn : IsConnected S)
    (hS : IsEmbeddedSliceOfOrder I (r : ℕ∞ω) 1 S) (htg : IsTotallyGeodesicFinite g S) :
    ∃ b : AddCircle (1 : ℝ) → M, ContMDiff 𝓘(ℝ, ℝ) I ((r - 1 : ℕ∞) : ℕ∞ω) b ∧ Injective b ∧
      range b = S ∧ ∃ R : M → AddCircle (1 : ℝ), (∀ s, R (b s) = s) ∧
        ∀ x ∈ S, ContMDiffAt I 𝓘(ℝ, ℝ) ((r - 1 : ℕ∞) : ℕ∞ω) R x := by
  obtain ⟨p, ℓ, hℓ, hunit, hper, hinj, hSeq⟩ :=
    exists_closedGeodesic_of_slice_dim_one g hr hnorm hSc hconn hS htg
  obtain ⟨b, -, hb, hbinj, hbr, R, hRb, hR⟩ :=
    soulBase_closedGeodesic g hr hnorm p hℓ hunit hper hinj
  refine ⟨b, hb, hbinj, hbr.trans hSeq.symm, R, hRb, fun x hx => hR x ?_⟩
  rwa [← hSeq]

/-- **The circle base map is an immersion**: `dR ∘ db = id` at every parameter, so `db` is
injective. -/
theorem soulBase_closedGeodesic_mfderiv_injective
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : TangentBundle I M) {ℓ : ℝ} (hℓ : 0 < ℓ) (hunit : g.inner p.proj p.snd p.snd = 1)
    (hper : g.geodesicFlow p ℓ = p) (hinj : InjOn (fun t => (g.geodesicFlow p t).proj) (Ico 0 ℓ)) :
    ∃ b : AddCircle (1 : ℝ) → M, range b = range (fun t => (g.geodesicFlow p t).proj) ∧
      ∀ s, Injective (mfderiv 𝓘(ℝ, ℝ) I b s) := by
  obtain ⟨b, -, hb, -, hbr, R, hRb, hR⟩ :=
    soulBase_closedGeodesic g hr hnorm p hℓ hunit hper hinj
  refine ⟨b, hbr, fun s => ?_⟩
  have hn : ((r - 1 : ℕ∞) : ℕ∞ω) ≠ 0 := by
    have h1 : (1 : ℕ∞) ≤ r - 1 := soulCarrier_one_le_sub_one hr
    have h1' : (1 : ℕ∞ω) ≤ ((r - 1 : ℕ∞) : ℕ∞ω) := by exact_mod_cast h1
    exact (zero_lt_one.trans_le h1').ne'
  have hbd : MDifferentiableAt 𝓘(ℝ, ℝ) I b s := (hb s).mdifferentiableAt hn
  have hRd : MDifferentiableAt I 𝓘(ℝ, ℝ) R (b s) :=
    (hR (b s) (hbr ▸ mem_range_self s)).mdifferentiableAt hn
  have hcomp := mfderiv_comp s hRd hbd
  have hid : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (R ∘ b) s = ContinuousLinearMap.id ℝ _ := by
    have heq : R ∘ b = id := funext hRb
    rw [heq, mfderiv_id]
  have key : ∀ u, mfderiv I 𝓘(ℝ, ℝ) R (b s) (mfderiv 𝓘(ℝ, ℝ) I b s u) = u := fun u => by
    have h := congrArg (fun L : TangentSpace 𝓘(ℝ, ℝ) s →L[ℝ] TangentSpace 𝓘(ℝ, ℝ) ((R ∘ b) s) =>
      L u) hcomp
    rw [hid] at h
    exact h.symm
  intro v w hvw
  rw [← key v, ← key w, hvw]

end DifferentialGeometry.Geometry.FiniteSoul
