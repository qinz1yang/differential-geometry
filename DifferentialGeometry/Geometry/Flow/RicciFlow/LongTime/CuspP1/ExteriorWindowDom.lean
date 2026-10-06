import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.CompactPatchMain
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ExteriorKernel

/-!
# CP1-D7 (1): core-side kernel constancy of the cusp torus, unconditional

`hdom` of `kernel_const_Ici_compact_CPD6` is only available for `t ≥ E.start` (the ball
`in_ball` is stated from `E.start`), so we weaken the base time of a patch from `cores.start` to
`E.start` and use `kernel_const_Ici_pointwise_CPD6` with `T₀ = E.start`.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {K : ℕ} {slices : ℕ → RegularSlice F.observation}

/-- A patch with base time `T` is a patch with any later base time `T'`. -/
def patchMonoBase_CPD7 {H : FiniteVolumeHyperbolicModel.{u}} {T T' : ℝ}
    (hTT : T ≤ T') {α : ℝ → ℝ} {domain : ℝ → TopologicalSpace.Opens H.Carrier}
    {f : (t : ℝ) → T ≤ t → H.Carrier → (postStage F.observation t).Carrier} {t₀ : ℝ}
    {x₀ : H.Carrier} (p : PersistentModelPatch F H T α domain f t₀ x₀) :
    PersistentModelPatch F H T' α domain (fun t ht => f t (hTT.trans ht)) t₀ x₀ where
  n := p.n
  first := p.first
  last := p.last
  ordered := p.ordered
  a := p.a
  b := p.b
  a_nonneg := p.a_nonneg
  before := p.before
  after := p.after
  horizon := p.horizon
  neighborhood := p.neighborhood
  mem_neighborhood := p.mem_neighborhood
  in_domain := fun t ht hT => p.in_domain t ht (hTT.trans hT)
  stages := p.stages
  map := p.map
  smooth := p.smooth
  agrees := fun t ht hT x hx => p.agrees t ht (hTT.trans hT) x hx
  speed := fun t ht hT x hx => p.speed t ht (hTT.trans hT) x hx

theorem kernel_portLoop_const_CPD7 {L : LateCutFamily F K slices}
    (E : PersistentCuspExterior L.cores) (i : Fin L.cores.count)
    (q : Fin (E.truncation i).count) (x : Torus) {s t : ℝ} (hs : E.start ≤ s) (ht : E.start ≤ t) :
    (FundamentalGroup.map (portLoopMap_CPH E i q s hs) x).ker =
      (FundamentalGroup.map (portLoopMap_CPH E i q t ht) x).ker := by
  let ι : C(Torus, (L.cores.model i).Carrier) :=
    ⟨fun z => (E.truncation i).cuspMap q (z, halfZero), by
      have := ((E.truncation i).cuspEmbedding q).contMDiff.continuous
      exact this.comp (continuous_id.prodMk continuous_const)⟩
  have hdom : ∀ τ (hτ : E.start ≤ τ) (y : Torus), ι y ∈ L.cores.domain i τ := by
    intro τ hτ y
    show (E.truncation i).cuspMap q (y, halfZero) ∈ _
    rw [(E.truncation i).cusp_zero q y]
    exact L.cores.advertised_ball i τ (E.after_cores.trans hτ) (E.in_ball i τ hτ ⟨_, rfl⟩)
  refine kernel_const_Ici_pointwise_CPD6 (F := F) (T₀ := E.start) (α := L.cores.accuracy)
    (domain := L.cores.domain i)
    (f := fun t ht => L.cores.map i t (E.after_cores.trans ht)) ι ?_
    (fun t ht => portLoopMap_CPH E i q t ht) (fun t ht y => rfl) x hs ht
  intro τ hτ y
  have h := L.cores.static_patches i τ (E.after_cores.trans hτ) (ι y) (hdom τ hτ y)
  exact ⟨ι y, patchMonoBase_CPD7 E.after_cores h.some, h.some.mem_neighborhood⟩

end GC.LongTime.CuspP1
