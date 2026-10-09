import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainExports74
import DifferentialGeometry.Geometry.Fibration.ActualStageChainSlimZeroFaces

/-!
# Draft 74, S0 on the member: a zero-face end of a slim arc is a whole model face

Lane C14-REG-CHAIN (by S-REG-CHAIN5), G38. A zero-face end of an arc of `D₃` (a point `y` of the
base face set `F₃`) has as end fibre `f₃⁻¹{y}` ONE whole zero face `∂Z_k`
(`zsp03_slim_face_fibre_ZSP35`: a face meeting `U` is one whole slim fibre; this replaces the
route through invariance of domain). Carried to `W` by `M.ψ`, the `ψ`-image of that fibre is the
model boundary `pieceBoundary (zero.rows.piece i)` of the zero piece (`ZeroLink_LND74`); when it
is preconnected (it is the image of a standard whole fibre `S²` / `T²`) it is a single actual
model boundary face:

* `slim_zero_end_fibre74`: `y ∈ F₃ → ∃ k, f₃⁻¹{y} = ∂Z_k` (chain level);
* `exists_zeroFace_of_preconnected74`: kernel on `W`: a preconnected nonempty `s` equal to the
  model boundary image of a zero piece is `neighbourSet` of a model face;
* `ClosedChainEZRowsSource_RGC.zero_end_face74`: for the closed route, the `M.ψ`-image of the
  end fibre over `y ∈ F₃` is `neighbourSet F` for a neighbour face `F` of the zero exit.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open GC.GraphManifold GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

namespace Gaf02ChainEJA

variable {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
  {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz oM}

/-- **The fibre over a face point is one whole zero face**: for `y ∈ F₃`, `f₃⁻¹{y} = ∂Z_k` for
some zero index `k`. -/
theorem slim_zero_end_fibre74
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) {y : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hy : y ∈ C.slimFacePoints_ZSP35) :
    ∃ k : P.zero.finite_centres.toFinset, C.slimMap_ZSP35 ⁻¹' {y} =
      frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E) := by
  obtain ⟨k, hk⟩ := mem_iUnion.mp hy
  obtain ⟨p, ⟨hpF, hpU⟩, rfl⟩ := hk
  exact ⟨k, C.zsp03_slim_face_fibre_ZSP35 hεr k hpF hpU⟩

end Gaf02ChainEJA

section Kernel

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} {Zr : ZeroDomains W}
  {Cu : CuspCores W E}

/-- **A preconnected model boundary image is a single model face**: if a nonempty preconnected
set `s` is the model boundary image of the zero piece `i`, then `s = neighbourSet F` for a
neighbour face `F`. -/
theorem exists_zeroFace_of_preconnected74 (i : Fin Zr.count) {s : Set W.Carrier}
    (hs : IsPreconnected s) (hne : s.Nonempty) (h : s = pieceBoundary (Zr.piece i)) :
    ∃ F : NeighbourFace Zr Cu, s = neighbourSet F := by
  have hemb : Topology.IsClosedEmbedding (Zr.piece i).map :=
    (Zr.piece i).continuous_map.isClosedEmbedding (Zr.piece i).injective
  have hB : IsPreconnected ((𝓡∂ 3).boundary (Zr.piece i).Piece) :=
    hemb.isInducing.isPreconnected_image.mp (by rw [← pieceBoundary]; rw [← h]; exact hs)
  obtain ⟨x, hx⟩ : ((𝓡∂ 3).boundary (Zr.piece i).Piece).Nonempty := by
    obtain ⟨z, hz⟩ := hne
    rw [h] at hz
    obtain ⟨x, hx, -⟩ := hz
    exact ⟨x, hx⟩
  refine ⟨Sum.inl ⟨i, ActualComponent.of hx⟩, ?_⟩
  change s = (Zr.piece i).map '' connectedComponentIn _ x
  rw [hB.connectedComponentIn hx, h]
  rfl

end Kernel

namespace ClosedChainEZRowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}

/-- **The end fibre over a face point, carried to `W`, is a neighbour model face**: for the
closed route, `y ∈ F₃` and a preconnected `M.ψ`-image of `f₃⁻¹{y}` (the image of a standard whole
fibre), `M.ψ(f₃⁻¹{y}) = neighbourSet F` for a neighbour face `F` of the zero exit. -/
theorem zero_end_face74 (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz)
    (zero : ZSP02SmoothExit74 S) {n : ℕ} {E : BoundaryTori W n} {Cu : CuspCores W E}
    (hεr : εr < 1 / 2) {y : ClosedBlock74 S} (hy : y ∈ S.chain.slimFacePoints_ZSP35)
    (hs : IsPreconnected (M.ψ '' (S.chain.slimMap_ZSP35 ⁻¹' {y})))
    (hne : (M.ψ '' (S.chain.slimMap_ZSP35 ⁻¹' {y})).Nonempty) :
    ∃ F : NeighbourFace zero.rows Cu,
      M.ψ '' (S.chain.slimMap_ZSP35 ⁻¹' {y}) = neighbourSet F := by
  obtain ⟨k, hk⟩ := S.chain.slim_zero_end_fibre74 hεr hy
  obtain ⟨σ, hσ⟩ := zero.link
  obtain ⟨-, hbd, -⟩ := hσ (σ.symm k)
  rw [σ.apply_symm_apply] at hbd
  refine exists_zeroFace_of_preconnected74 (σ.symm k) hs hne ?_
  rw [hbd, hk]
  rfl

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
