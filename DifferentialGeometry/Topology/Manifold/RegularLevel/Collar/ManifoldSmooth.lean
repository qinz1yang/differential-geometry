import DifferentialGeometry.Topology.Manifold.RegularLevel.Collar.ManifoldFlow
import DifferentialGeometry.Topology.Manifold.RegularLevel.Collar.LevelAtlas
import DifferentialGeometry.Topology.Manifold.SmoothTwoSidedCollar

set_option autoImplicit false
open Set Manifold
open scoped Topology ContDiff
open DifferentialGeometry.Topology.Morse Poincare.Topology
noncomputable section
namespace Poincare.Manifold.RegularLevel

variable {m : ℕ} {H : Type*} [TopologicalSpace H]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ (MorseModel (m + 1)) H)
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

theorem exists_smoothTwoSidedCollar_of_compact_regularLevel_manifold
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (a : ℝ)
    (hK : IsCompact {x | f x = a})
    (hr : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) :
    let _ := levelChartedSpace I hf hr
    ∃ c : SmoothTwoSidedCollar 𝓘(ℝ, MorseModel m) I
      (Subtype.val : {y : M // f y = a} → M),
      ∀ p, f (c.toFun p) = a - p.2 := by
  let _ := levelChartedSpace I hf hr
  obtain ⟨r, hrpos, U, F, hF, e, hforward, hback, htime, hvalue, hzero⟩ :=
    exists_flowCollar_of_compact_regularLevel_manifold I hf a hK hr
  let e' : ({y : M // f y = a} × symmetricOpenInterval r) ≃ₜ U := e
  have hinc : ContMDiff 𝓘(ℝ, MorseModel m) I ∞
      (Subtype.val : {y : M // f y = a} → M) := contMDiff_level_inclusion I hf hr
  have he : ContMDiff (𝓘(ℝ, MorseModel m).prod 𝓘(ℝ, ℝ)) I ∞
      (e' : {y : M // f y = a} × symmetricOpenInterval r → U) := by
    apply (ContMDiff.subtypeVal_comp_iff U e').mp
    have hp : ContMDiff (𝓘(ℝ, MorseModel m).prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun p : {y : M // f y = a} × symmetricOpenInterval r => ((p.1 : M), (p.2 : ℝ))) :=
      (hinc.comp contMDiff_fst).prodMk (contMDiff_subtype_val.comp contMDiff_snd)
    exact (hF.comp hp).congr (fun p => hforward p)
  have hproj : ContMDiff I I ∞ (fun y : U => F (y, f y - a)) :=
    hF.comp (contMDiff_subtype_val.prodMk ((hf.comp contMDiff_subtype_val).sub contMDiff_const))
  have hprojlevel : ∀ y : U, f (F (y, f y - a)) = a := by
    intro y
    rw [← hback y]
    exact (e'.symm y).1.2
  have hinv₁ : ContMDiff I 𝓘(ℝ, MorseModel m) ∞ (fun y : U => (e'.symm y).1) := by
    apply (contMDiff_level_factor I hf hr hproj hprojlevel).congr
    intro y
    apply Subtype.ext
    exact hback y
  have hinv₂ : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y : U => ((e'.symm y).2 : symmetricOpenInterval r)) := by
    apply (ContMDiff.subtypeVal_comp_iff (symmetricOpenInterval r) _).mp
    exact (contMDiff_const.sub (hf.comp contMDiff_subtype_val)).congr (fun y => htime y)
  let c : SmoothTwoSidedCollar 𝓘(ℝ, MorseModel m) I
      (Subtype.val : {y : M // f y = a} → M) :=
    { radius := r
      radius_pos := hrpos
      neighborhood := U
      toDiffeomorph :=
        { toEquiv := e'.toEquiv
          contMDiff_toFun := he
          contMDiff_invFun := hinv₁.prodMk hinv₂ }
      zero_eq := hzero }
  exact ⟨c, hvalue⟩

end Poincare.Manifold.RegularLevel
