import DifferentialGeometry.Topology.Manifold.EmbeddedHypersurface.DefiningFunction
import DifferentialGeometry.Topology.Manifold.RegularLevel.Collar.ManifoldSmooth

open Set DifferentialGeometry.Topology.Morse DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology
set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Manifold.EmbeddedHypersurface

private theorem exists_flatten_open_diffeomorph
    {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace G] [TopologicalSpace M] [ChartedSpace G M]
    (J : ModelWithCorners ℝ E G) (U : TopologicalSpace.Opens M)
    (W : TopologicalSpace.Opens U) :
    ∃ O : TopologicalSpace.Opens M, ∃ d : Diffeomorph J J W O ∞,
      ∀ w, (d w : M) = ((w : U) : M) := by
  let g : W → M := fun w => ((w : U) : M)
  have hg : Topology.IsOpenEmbedding g :=
    U.isOpen.isOpenEmbedding_subtypeVal.comp W.isOpen.isOpenEmbedding_subtypeVal
  let O : TopologicalSpace.Opens M := ⟨range g, hg.isOpen_range⟩
  let h : W ≃ₜ O := hg.isEmbedding.toHomeomorph
  have hforward : ContMDiff J J ∞ (h : W → O) := by
    apply (ContMDiff.subtypeVal_comp_iff O h).mp
    change ContMDiff J J ∞ g
    exact (contMDiff_subtype_val (I := J) (U := U)).comp
      (contMDiff_subtype_val (I := J) (U := W))
  have hback : ContMDiff J J ∞ (h.symm : O → W) := by
    apply (ContMDiff.subtypeVal_comp_iff W h.symm).mp
    apply (ContMDiff.subtypeVal_comp_iff U _).mp
    exact contMDiff_subtype_val.congr
      (fun y => congrArg (fun z : O => (z : M)) (h.apply_symm_apply y))
  exact ⟨O, ⟨h.toEquiv, hforward, hback⟩, fun _ => rfl⟩

variable {m : ℕ} {H G S M : Type*}
  [TopologicalSpace H] [TopologicalSpace G]
  [TopologicalSpace S] [ChartedSpace H S]
  [TopologicalSpace M] [ChartedSpace G M]
  (I : ModelWithCorners ℝ (MorseModel m) H)
  (J : ModelWithCorners ℝ (MorseModel (m + 1)) G)
  [I.Boundaryless] [J.Boundaryless] [IsManifold J ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem nonempty_smoothTwoSidedCollar {e : S → M}
    (he : Manifold.IsSmoothEmbedding I J ∞ e) (hK : IsCompact (range e))
    (V : ∀ s, TangentSpace J (e s))
    (hV : Continuous (fun s => (⟨e s, V s⟩ : TangentBundle J M)))
    (htrans : ∀ s, V s ∉ (mfderiv I J e s).range) :
    Nonempty (SmoothTwoSidedCollar I J e) := by
  obtain ⟨U, hU, f, hf, hzero, hlevelCompact, hreg⟩ :=
    exists_regular_definingFunction I J he hK V hV htrans
  let _ : SecondCountableTopology G := J.secondCountableTopology
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact G M
  let _ : LocallyCompactSpace G := J.locallyCompactSpace
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace G M
  let _ : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  let _ := RegularLevel.levelChartedSpace J hf hreg
  let L := {y : U // f y = 0}
  let eU : S → U := fun s => ⟨e s, hU (mem_range_self s)⟩
  let eL : S → L := fun s => ⟨eU s, (hzero (eU s)).mpr (mem_range_self s)⟩
  have heU : ContMDiff I J ∞ eU :=
    (ContMDiff.subtypeVal_comp_iff U eU).mp he.contMDiff
  have heL : ContMDiff I 𝓘(ℝ, MorseModel m) ∞ eL :=
    RegularLevel.contMDiff_level_factor J hf hreg heU (fun s => (eL s).2)
  have hEmb : Topology.IsEmbedding eL := Topology.IsEmbedding.of_comp heL.continuous
    (continuous_subtype_val.comp continuous_subtype_val) he.isEmbedding
  have hSurj : Function.Surjective eL := by
    intro y
    obtain ⟨s, hs⟩ := (hzero y.1).mp y.2
    refine ⟨s, Subtype.ext (Subtype.ext hs)⟩
  let h : S ≃ₜ L :=
    (Equiv.ofBijective eL ⟨hEmb.injective, hSurj⟩).toHomeomorphOfIsInducing hEmb.isInducing
  have hIncl : ContMDiff 𝓘(ℝ, MorseModel m) J ∞ (fun y : L => ((y : U) : M)) :=
    contMDiff_subtype_val.comp (RegularLevel.contMDiff_level_inclusion J hf hreg)
  have hback : ContMDiff 𝓘(ℝ, MorseModel m) I ∞ (h.symm : L → S) := by
    apply (ContMDiff.iff_comp_isImmersion he.isImmersion).mpr
    refine ⟨h.symm.continuous, hIncl.congr ?_⟩
    intro y
    exact congrArg (fun z : L => ((z : U) : M)) (h.apply_symm_apply y)
  let d : Diffeomorph I 𝓘(ℝ, MorseModel m) S L ∞ := ⟨h.toEquiv, heL, hback⟩
  obtain ⟨c, _⟩ := RegularLevel.exists_smoothTwoSidedCollar_of_compact_regularLevel_manifold
    J hf 0 hlevelCompact hreg
  obtain ⟨O, dO, hdO⟩ := exists_flatten_open_diffeomorph J U c.neighborhood
  let dprod := d.prodCongr (Diffeomorph.refl 𝓘(ℝ, ℝ) (symmetricOpenInterval c.radius) ∞)
  refine ⟨{
    radius := c.radius
    radius_pos := c.radius_pos
    neighborhood := O
    toDiffeomorph := (dprod.trans c.toDiffeomorph).trans dO
    zero_eq := ?_ }⟩
  intro s
  change (dO (c.toDiffeomorph (d s, ⟨0, neg_lt_zero.mpr c.radius_pos, c.radius_pos⟩)) : M) = e s
  rw [hdO]
  exact congrArg (fun y : U => (y : M)) (c.zero_eq (d s))

end DifferentialGeometry.Manifold.EmbeddedHypersurface
