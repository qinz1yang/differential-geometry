import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThinBoundaryCollar

/-!
# CH12-S34 G1': injectivity / embedding / immersion of a lift through a smooth map

If `c ∘ L = φ` on `cuspDomain` with `c`, `L` smooth, then `L` inherits injectivity, the embedding
property and the immersion property of `φ`.  (Used with `c = rmapK_S12 F` and `c = cutPieceMap D j`.)
-/

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
  GC.Endpoint
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

section Props

variable {W₀ P : CompactCarrier.{u}} (c : P.Carrier → W₀.Carrier)
  (L : CuspHalfSpace → P.Carrier) (φ : CuspHalfSpace → W₀.Carrier)

theorem injOn_lift_S34 (hb : ∀ p ∈ cuspDomain, c (L p) = φ p)
    (hφ : InjOn φ cuspDomain) : InjOn L cuspDomain := fun p hp q hq h =>
  hφ hp hq (by rw [← hb p hp, ← hb q hq, h])

theorem isEmbedding_lift_S34 (hc : ContMDiff P.model W₀.model ∞ c)
    (hL : ContMDiffOn halfCollarModel P.model ∞ L cuspDomain)
    (hb : ∀ p ∈ cuspDomain, c (L p) = φ p)
    (hφ : _root_.Topology.IsEmbedding (fun p : cuspDomain => φ p)) :
    _root_.Topology.IsEmbedding (fun p : cuspDomain => L p) := by
  have hLc : Continuous (fun p : cuspDomain => L p) := hL.continuousOn.domRestrict
  refine _root_.Topology.IsEmbedding.of_comp hLc hc.continuous ?_
  have : (c ∘ fun p : cuspDomain => L p) = fun p : cuspDomain => φ p :=
    funext fun p => hb p p.2
  rw [this]; exact hφ

theorem immersion_lift_S34 (hc : ContMDiff P.model W₀.model ∞ c)
    (hL : ContMDiffOn halfCollarModel P.model ∞ L cuspDomain)
    (hb : ∀ p ∈ cuspDomain, c (L p) = φ p)
    (hφ : ∀ p ∈ cuspDomain, Function.Injective (mfderiv halfCollarModel W₀.model φ p)) :
    ∀ p ∈ cuspDomain, Function.Injective (mfderiv halfCollarModel P.model L p) := by
  intro p hp
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by decide
  have hnhds : cuspDomain ∈ nhds p := isOpen_cuspDomain_C4.mem_nhds hp
  have hLd : MDifferentiableAt halfCollarModel P.model L p :=
    (hL.contMDiffAt hnhds).mdifferentiableAt hn
  have hcd : MDifferentiableAt P.model W₀.model c (L p) := (hc (L p)).mdifferentiableAt hn
  have hev : φ =ᶠ[nhds p] c ∘ L :=
    Filter.eventuallyEq_of_mem hnhds (fun q hq => (hb q hq).symm)
  have hder : mfderiv halfCollarModel W₀.model φ p =
      (mfderiv P.model W₀.model c (L p)).comp (mfderiv halfCollarModel P.model L p) := by
    rw [hev.mfderiv_eq]
    exact mfderiv_comp p hcd hLd
  have hder' : ∀ a, mfderiv halfCollarModel W₀.model φ p a =
      mfderiv P.model W₀.model c (L p) (mfderiv halfCollarModel P.model L p a) :=
    fun a => by rw [hder]; rfl
  intro a b hab
  exact hφ p hp ((hder' a).trans ((congrArg (mfderiv P.model W₀.model c (L p)) hab).trans
    (hder' b).symm))

end Props

end GC.LongTime.Ch12
