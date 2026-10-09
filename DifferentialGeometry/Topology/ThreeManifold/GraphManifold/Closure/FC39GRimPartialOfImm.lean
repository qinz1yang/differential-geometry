import DifferentialGeometry.Topology.Manifold.OpenEmbedding
import DifferentialGeometry.Topology.Manifold.OpenSubtype

/-!
# FC39 GROUP G, RIMBOX (sheet §3 K7): a partial diffeomorphism from an injective immersion

Lane FC39-G-RIMBOX. Between manifolds over boundaryless models of the same finite dimension, a map
that is smooth, injective and immersive on an open set `Ω` is a partial diffeomorphism with source
`Ω` and target `f '' Ω` (`exists_partialDiffeomorph_of_injOn_immersion_GRIM`; the inverse function
theorem on `Ω` through `exists_diffeomorph_onto_range_of_injective_immersion`). This turns the rim
parametrization (`rimParam_props_GRIM`) into the rim chart.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

/-- **A partial diffeomorphism from an injective immersion on an open set.** -/
theorem exists_partialDiffeomorph_of_injOn_immersion_GRIM [Nonempty M] (f : M → N) {Ω : Set M}
    (hΩ : IsOpen Ω) (hf : ContMDiffOn I J ∞ f Ω) (hinj : InjOn f Ω)
    (himm : ∀ x ∈ Ω, Injective (mfderiv I J f x))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    ∃ φ : PartialDiffeomorph I J M N ∞, φ.source = Ω ∧ φ.target = f '' Ω ∧ ∀ x, φ x = f x := by
  classical
  let M' : TopologicalSpace.Opens M := ⟨Ω, hΩ⟩
  let f' : M' → N := fun x => f x
  have hf' : ContMDiff I J ∞ f' := fun x =>
    (hf.contMDiffAt (hΩ.mem_nhds x.2)).comp x (contMDiff_subtype_val x)
  have hinj' : Injective f' := fun x y h => Subtype.ext (hinj x.2 y.2 h)
  have himm' : ∀ x, Injective (mfderiv I J f' x) := fun x => by
    rw [DifferentialGeometry.mfderiv_restrict_open f M' x]
    exact himm x x.2
  obtain ⟨V, Φ, hV, hΦ, hΦs⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_diffeomorph_onto_range_of_injective_immersion
      f' hf' hinj' himm' hdim
  have hVeq : (V : Set N) = f '' Ω := by
    rw [hV]
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  let g : N → M := fun y => if h : y ∈ V then ((Φ.symm ⟨y, h⟩ : M') : M) else Classical.arbitrary M
  have hg : ∀ (y : N) (h : y ∈ V), g y = ((Φ.symm ⟨y, h⟩ : M') : M) := fun y h => by
    simp [g, h]
  refine ⟨{ toFun := f
            invFun := g
            source := Ω
            target := V
            map_source' := fun x hx => by
              rw [hVeq]
              exact ⟨x, hx, rfl⟩
            map_target' := fun y hy => by rw [hg y hy]; exact (Φ.symm ⟨y, hy⟩).2
            left_inv' := fun x hx => by
              have hfx : f x ∈ V := by
                change f x ∈ (V : Set N)
                rw [hVeq]
                exact ⟨x, hx, rfl⟩
              change g (f x) = x
              rw [hg _ hfx]
              have h1 : (⟨f x, hfx⟩ : V) = Φ ⟨x, hx⟩ := Subtype.ext (hΦ ⟨x, hx⟩).symm
              rw [h1, Φ.symm_apply_apply]
            right_inv' := fun y hy => by
              rw [hg y hy]
              exact hΦs ⟨y, hy⟩
            open_source := hΩ
            open_target := V.isOpen
            contMDiffOn_toFun := hf
            contMDiffOn_invFun := fun y hy => by
              have hsub : ContMDiffAt J I ∞ (fun z : V => g z) ⟨y, hy⟩ := by
                have h1 : ContMDiffAt J I ∞ (fun z : V => ((Φ.symm z : M') : M)) ⟨y, hy⟩ :=
                  (contMDiff_subtype_val.comp Φ.symm.contMDiff) _
                refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
                exact hg z z.2
              exact (contMDiffAt_subtype_iff.mp hsub).contMDiffWithinAt }, rfl, hVeq, fun _ => rfl⟩

end GC.GraphManifold.Assembly.FC39P0
