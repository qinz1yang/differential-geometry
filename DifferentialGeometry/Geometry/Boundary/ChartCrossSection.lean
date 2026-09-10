import DifferentialGeometry.Geometry.Boundary.FullRankFactorization
import DifferentialGeometry.Geometry.Boundary.SmoothFactorization
import Mathlib.Geometry.Manifold.Diffeomorph

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff

namespace Poincare.Geometry.Boundary

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

theorem exists_boundaryLevel_diffeomorph_of_product_chart
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
    (O : TopologicalSpace.Opens (N × ℝ)) (V : TopologicalSpace.Opens M)
    (Φ : O ≃ₘ⟮K.prod 𝓘(ℝ), J⟯ V) (t : ℝ) (hsection : ∀ p : N, (p, t) ∈ O)
    (u : W → ℝ) (a b : ℝ) (hab : a ≠ b) (hu : Continuous u)
    (hboundary : ∀ w, I.IsBoundaryPoint w → u w = a ∨ u w = b)
    (himage : ι '' {w : W | I.IsBoundaryPoint w ∧ u w = a} =
      range (fun p : N ↦ (Φ ⟨(p, t), hsection p⟩ : M))) :
    ∃ η : N ≃ₘ⟮K, hI.boundaryI⟯ boundaryLevel u a b hab hu hboundary,
      ∀ p, ι (η p).1.1 = (Φ ⟨(p, t), hsection p⟩ : M) := by
  classical
  let B := boundaryLevel u a b hab hu hboundary
  let sectionMap : N → O := fun p ↦ ⟨(p, t), hsection p⟩
  let q : N → M := fun p ↦ (Φ (sectionMap p) : M)
  have hsectionSmooth : ContMDiff K (K.prod 𝓘(ℝ)) ∞ sectionMap :=
    (ContMDiff.subtypeVal_comp_iff O sectionMap).mp (contMDiff_id.prodMk contMDiff_const)
  have hq : ContMDiff K J ∞ q :=
    contMDiff_subtype_val.comp (Φ.contMDiff.comp hsectionSmooth)
  have hpre (p : N) : ∃ w : W, (I.IsBoundaryPoint w ∧ u w = a) ∧ ι w = q p := by
    have hp : q p ∈ range (fun p : N ↦ (Φ ⟨(p, t), hsection p⟩ : M)) := ⟨p, rfl⟩
    rw [← himage] at hp
    exact hp
  choose f hf hfeq using hpre
  let forward : N → B := fun p ↦ ⟨⟨f p, (hf p).1⟩, (hf p).2⟩
  have hforward : ContMDiff K hI.boundaryI ∞ forward := by
    apply (contMDiff_boundaryLevelInclusion_comp_iff u a b hab hu hboundary).mp
    apply (contMDiff_iff_comp_of_fullRank_embedding hι hemb hinj hdim f).mpr
    have heq : ι ∘ f = q := funext hfeq
    rwa [heq]
  have hsurj : Function.Surjective forward := by
    intro x
    have hx : ι x.1.1 ∈ ι '' {w : W | I.IsBoundaryPoint w ∧ u w = a} :=
      ⟨x.1.1, ⟨x.1.2, x.2⟩, rfl⟩
    rw [himage] at hx
    obtain ⟨p, hp⟩ := hx
    refine ⟨p, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hemb.injective ((hfeq p).trans hp)
  have htarget (x : B) : ι x.1.1 ∈ V := by
    obtain ⟨p, rfl⟩ := hsurj x
    rw [hfeq]
    exact (Φ (sectionMap p)).property
  let toTarget : B → V := fun x ↦ ⟨ι x.1.1, htarget x⟩
  have htoTarget : ContMDiff hI.boundaryI J ∞ toTarget := by
    apply (ContMDiff.subtypeVal_comp_iff V toTarget).mp
    exact hι.comp (contMDiff_boundaryLevelInclusion u a b hab hu hboundary)
  let back : B → N := fun x ↦ (Φ.symm (toTarget x) : N × ℝ).1
  have hback : ContMDiff hI.boundaryI K ∞ back :=
    contMDiff_fst.comp (contMDiff_subtype_val.comp (Φ.symm.contMDiff.comp htoTarget))
  have hleft (p : N) : back (forward p) = p := by
    have htar : toTarget (forward p) = Φ (sectionMap p) := Subtype.ext (hfeq p)
    change (Φ.symm (toTarget (forward p)) : N × ℝ).1 = p
    rw [htar, Φ.symm_apply_apply]
  have hright (x : B) : forward (back x) = x := by
    obtain ⟨p, rfl⟩ := hsurj x
    rw [hleft]
  exact ⟨⟨⟨forward, back, hleft, hright⟩, hforward, hback⟩, hfeq⟩

end Poincare.Geometry.Boundary
