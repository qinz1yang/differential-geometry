import Poincare.Analysis.LocalDerivativeHomotopy
import Poincare.Topology.Homology.RelativeHomeomorphism
import Poincare.Topology.Homology.RelativeZero
import Mathlib.Analysis.Convex.Contractible

noncomputable section

open Filter Set
open scoped Topology

universe u

namespace Poincare.Topology

theorem exists_ball_relative_homologyMap_eq_derivative
    {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    (A : E ≃L[ℝ] F) (hzero : f 0 = 0)
    (hf : HasFDerivAt f (A : E →L[ℝ] F) 0)
    {s : Set E} (hs : s ∈ 𝓝 (0 : E)) (hc : ContinuousOn f s) :
    ∃ (r : ℝ) (hr : 0 < r), Metric.ball (0 : E) r ⊆ s ∧
      ∃ g h : C(Metric.ball (0 : E) r, F),
        (∀ x, g x = A (x : E)) ∧ (∀ x, h x = f (x : E)) ∧
        ∃ hg : MapsTo g
            ({(⟨0, Metric.mem_ball_self hr⟩ : Metric.ball (0 : E) r)}ᶜ : Set _)
            ({0}ᶜ : Set F),
          ∃ hh : MapsTo h
              ({(⟨0, Metric.mem_ball_self hr⟩ : Metric.ball (0 : E) r)}ᶜ : Set _)
              ({0}ᶜ : Set F),
            ∀ n : ℕ, integralRelativeHomologyMap (n + 1) h hh =
              integralRelativeHomologyMap (n + 1) g hg := by
  obtain ⟨r, hr, hrs, g₀, h₀, hg₀, hh₀, H, _⟩ :=
    Poincare.Analysis.exists_punctured_ball_derivative_homotopy A hzero hf hs hc
  let B : Set E := Metric.ball (0 : E) r
  let z : B := ⟨0, Metric.mem_ball_self hr⟩
  let V : Set B := {z}ᶜ
  let U : Set E := Metric.ball (0 : E) r \ {0}
  have hne (x : V) : ((x : B) : E) ≠ 0 := by
    intro hx
    exact x.property (Subtype.ext hx)
  let k : C(V, U) :=
    ⟨fun x => ⟨((x : B) : E), ⟨(x : B).property, hne x⟩⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  let g : C(B, F) :=
    ⟨fun x => A (x : E), A.continuous.comp continuous_subtype_val⟩
  let h : C(B, F) :=
    ⟨fun x => f (x : E),
      hc.comp_continuous continuous_subtype_val (fun x => hrs x.property)⟩
  have hg : MapsTo g V ({0}ᶜ : Set F) := by
    intro x hx hz
    have hxzero : (x : E) = 0 := A.injective (hz.trans (map_zero A).symm)
    exact hx (Subtype.ext hxzero)
  have hh : MapsTo h V ({0}ᶜ : Set F) := by
    intro x hx
    have hval := hh₀ (k ⟨x, hx⟩)
    have hnonzero : (h₀ (k ⟨x, hx⟩) : F) ≠ 0 := (h₀ (k ⟨x, hx⟩)).property
    change f (x : E) ≠ 0
    rw [hval] at hnonzero
    exact hnonzero
  have hgcomp : g₀.comp k = singularPairRestriction g hg := by
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    exact hg₀ (k x)
  have hhcomp : h₀.comp k = singularPairRestriction h hh := by
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    exact hh₀ (k x)
  have hrestr : (singularPairRestriction g hg).Homotopic
      (singularPairRestriction h hh) := by
    rw [← hgcomp, ← hhcomp]
    exact ⟨H.compContinuousMap k⟩
  refine ⟨r, hr, hrs, g, h, (fun _ => rfl), (fun _ => rfl), hg, hh, ?_⟩
  intro n
  let := integralSingularHomology_subsingleton_of_contractible (n + 1)
    (Nat.succ_ne_zero n) F
  exact (integralRelativeHomologyMap_eq_of_restriction_homotopic n g h V
    ({0}ᶜ : Set F) hg hh hrestr).symm

theorem integralRelativeHomologyMap_eq_derivative
    {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : C(E, F)) (A : E ≃L[ℝ] F) (hzero : f 0 = 0)
    (hf : HasFDerivAt f (A : E →L[ℝ] F) 0)
    (hpair : MapsTo f ({0}ᶜ : Set E) ({0}ᶜ : Set F)) (n : ℕ) :
    integralRelativeHomologyMap n f hpair =
      integralRelativeHomologyMap n ⟨A, A.continuous⟩
        (show MapsTo A ({0}ᶜ : Set E) ({0}ᶜ : Set F) from
          fun _ hx h => hx (A.injective (h.trans (map_zero A).symm))) := by
  let L : C(E, F) := ⟨A, A.continuous⟩
  have hL : MapsTo L ({0}ᶜ : Set E) ({0}ᶜ : Set F) :=
    fun _ hx h => hx (A.injective (h.trans (map_zero A).symm))
  change integralRelativeHomologyMap n f hpair =
    integralRelativeHomologyMap n L hL
  cases n with
  | zero =>
    exact integralRelativeHomologyMap_zero_eq_of_joined f L
      ({0}ᶜ : Set E) ({0}ᶜ : Set F) hpair hL
      (fun _ => ⟨PathConnectedSpace.somePath _ _⟩)
  | succ n =>
    obtain ⟨r, hr, _, g, h, hg, hh, hgp, hhp, hcompare⟩ :=
      exists_ball_relative_homologyMap_eq_derivative A hzero hf
        (s := Set.univ) Filter.univ_mem f.continuous.continuousOn
    let U : Set E := Metric.ball (0 : E) r
    let J := integralLocalHomologyNeighborhoodIso (n + 1) (0 : E) U
      Metric.isOpen_ball (Metric.mem_ball_self hr)
    have hJmap : J.hom.hom =
        integralRelativeHomologyMap (n + 1) (singularSubspaceInclusion U)
          (neighborhoodPointComplement_mapsTo (0 : E) U (Metric.mem_ball_self hr)) :=
      integralLocalHomologyNeighborhoodIso_hom (n + 1) (0 : E) U
        Metric.isOpen_ball (Metric.mem_ball_self hr)
    have hsurj : Function.Surjective J.hom.hom := by
      intro a
      refine ⟨J.inv.hom a, ?_⟩
      exact congrArg (fun k => k.hom a) J.inv_hom_id
    have hcomp : (integralRelativeHomologyMap (n + 1) f hpair).comp J.hom.hom =
        (integralRelativeHomologyMap (n + 1) L hL).comp J.hom.hom := by
      simp only [hJmap]
      rw [← integralRelativeHomologyMap_comp, ← integralRelativeHomologyMap_comp]
      have hincf : f.comp (singularSubspaceInclusion U) = h := by
        apply ContinuousMap.ext
        intro x
        exact (hh x).symm
      have hincL : L.comp (singularSubspaceInclusion U) = g := by
        apply ContinuousMap.ext
        intro x
        exact (hg x).symm
      simpa only [hincf, hincL] using
        (show integralRelativeHomologyMap (n + 1) h hhp =
          integralRelativeHomologyMap (n + 1) g hgp from hcompare n)
    apply LinearMap.ext
    intro a
    obtain ⟨b, rfl⟩ := hsurj a
    exact LinearMap.congr_fun hcomp b

end Poincare.Topology
