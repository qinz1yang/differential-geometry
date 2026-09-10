import DifferentialGeometry.Geometry.Boundary.FullRankFactorization
import DifferentialGeometry.Geometry.Boundary.SmoothFactorization
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.Diffeomorph

noncomputable section
open Set Topology Manifold
open scoped ContDiff

namespace Poincare.Geometry.Boundary

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

theorem exists_boundaryLevel_diffeomorph_of_smooth_embedding
    {E H W F H' M G H'' N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace W] [ChartedSpace H W] [hI : HasSmoothBoundary E H I] [IsManifold I ∞ W]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace M] [ChartedSpace H' M] [IsManifold J ∞ M]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H'']
    {K : ModelWithCorners ℝ G H''} [TopologicalSpace N] [ChartedSpace H'' N]
    (ι : W → M) (hι : ContMDiff I J ∞ ι) (hemb : IsEmbedding ι)
    (hinj : ∀ w, Function.Injective (mfderiv I J ι w))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    (q : N → M) (hq : IsSmoothEmbedding K J ∞ q)
    (u : W → ℝ) (a b : ℝ) (hab : a ≠ b) (hu : Continuous u)
    (hboundary : ∀ w, I.IsBoundaryPoint w → u w = a ∨ u w = b)
    (himage : ι '' {w : W | I.IsBoundaryPoint w ∧ u w = a} = range q) :
    ∃ η : N ≃ₘ⟮K, hI.boundaryI⟯ boundaryLevel u a b hab hu hboundary,
      ∀ p, ι (η p).1.1 = q p := by
  let L := boundaryLevel u a b hab hu hboundary
  have hpre (p : N) : ∃ w : W, (I.IsBoundaryPoint w ∧ u w = a) ∧ ι w = q p := by
    have hp : q p ∈ range q := mem_range_self p
    rwa [← himage] at hp
  choose f hf hfeq using hpre
  let forward : N → L := fun p ↦ ⟨⟨f p, (hf p).1⟩, (hf p).2⟩
  have hforward : ContMDiff K hI.boundaryI ∞ forward := by
    apply (contMDiff_boundaryLevelInclusion_comp_iff u a b hab hu hboundary).mp
    apply (contMDiff_iff_comp_of_fullRank_embedding hι hemb hinj hdim f).mpr
    exact (funext hfeq : ι ∘ f = q) ▸ hq.contMDiff
  have htarget (x : L) : ι x.1.1 ∈ range q := by
    rw [← himage]
    exact ⟨x.1.1, ⟨x.1.2, x.2⟩, rfl⟩
  let toRange : L → range q := fun x ↦ ⟨ι x.1.1, htarget x⟩
  let back : L → N := hq.isEmbedding.toHomeomorph.symm ∘ toRange
  have hbackeq (x : L) : q (back x) = ι x.1.1 :=
    congrArg Subtype.val (hq.isEmbedding.toHomeomorph.apply_symm_apply (toRange x))
  have hback : ContMDiff hI.boundaryI K ∞ back := by
    apply (ContMDiff.iff_comp_isImmersion hq.isImmersion).mpr
    refine ⟨hq.isEmbedding.toHomeomorph.symm.continuous.comp ?_, ?_⟩
    · exact (hι.continuous.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
    · have hcomp : q ∘ back = fun x : L ↦ ι x.1.1 := funext hbackeq
      rw [hcomp]
      exact hι.comp (contMDiff_boundaryLevelInclusion u a b hab hu hboundary)
  have hleft (p : N) : back (forward p) = p :=
    hq.isEmbedding.injective ((hbackeq (forward p)).trans (hfeq p))
  have hright (x : L) : forward (back x) = x := by
    apply Subtype.ext
    apply Subtype.ext
    exact hemb.injective ((hfeq (back x)).trans (hbackeq x))
  exact ⟨⟨⟨forward, back, hleft, hright⟩, hforward, hback⟩, hfeq⟩

end Poincare.Geometry.Boundary
