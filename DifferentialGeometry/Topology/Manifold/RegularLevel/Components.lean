import DifferentialGeometry.Topology.Manifold.RegularLevel.Coordinates
import DifferentialGeometry.Topology.Manifold.ModelWithCorners
import DifferentialGeometry.Topology.Morse.CriticalPoint
import Mathlib.Analysis.Convex.Topology
open Set Metric Manifold
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Morse
namespace DifferentialGeometry.Manifold.RegularLevel
section Model

variable {m : ℕ} {H M : Type*} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] (I : ModelWithCorners ℝ (MorseModel (m + 1)) H)
  [I.Boundaryless] [IsManifold I ∞ M]
private theorem exists_open_isPreconnected_superlevel_inter_model
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {x : M} {a : ℝ}
    (hx : f x = a) (hr : mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) :
    ∃ V : Set M, IsOpen V ∧ x ∈ V ∧ IsPreconnected (V ∩ {y | a < f y}) := by
  obtain ⟨Φ, hxΦ, _, hcoord, _, _⟩ := exists_level_coordinates I hf hx hr
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp Φ.open_target (Φ x) (Φ.map_source hxΦ)
  let V := Φ.source ∩ Φ ⁻¹' ball (Φ x) r
  have hV : IsOpen V := Φ.toOpenPartialHomeomorph.isOpen_inter_preimage isOpen_ball
  have hxe : x ∈ V := ⟨hxΦ, mem_ball_self hr⟩
  have heq : V ∩ {y | a < f y} = Φ.symm ''
      (ball (Φ x) r ∩ {z | z (Fin.last m) < 0}) := by
    apply Subset.antisymm
    · rintro y ⟨⟨hy, hyball⟩, hyf⟩
      refine ⟨Φ y, ⟨hyball, ?_⟩, Φ.left_inv hy⟩
      rw [mem_ofPred_eq, hcoord y hy]
      exact sub_neg.mpr hyf
    · rintro y ⟨z, hz, rfl⟩
      have hzT := hball hz.1
      have hzS := Φ.map_target hzT
      have hzcoord := hcoord (Φ.symm z) hzS
      have hzval : Φ (Φ.symm z) (Fin.last m) = z (Fin.last m) :=
        congrArg (fun w : MorseModel (m + 1) => w (Fin.last m)) (Φ.right_inv hzT)
      refine ⟨⟨hzS, ?_⟩, ?_⟩
      · change Φ (Φ.symm z) ∈ ball (Φ x) r
        exact (congrArg (fun w => w ∈ ball (Φ x) r) (Φ.right_inv hzT)).mpr hz.1
      · change a < f (Φ.symm z)
        have hzlast : z (Fin.last m) < 0 := hz.2
        linarith
  refine ⟨V, hV, hxe, ?_⟩
  rw [heq]
  have hc : Convex ℝ {z : MorseModel (m + 1) | z (Fin.last m) < 0} :=
    convex_halfSpace_lt ⟨fun _ _ => rfl, fun _ _ => rfl⟩ 0
  exact ((convex_ball (Φ x) r).inter hc).isPreconnected.image Φ.symm
    (Φ.symm.contMDiffOn.continuousOn.mono (fun _ hz => hball hz.1))

end Model

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ E H) [I.Boundaryless] [IsManifold I ∞ M]

theorem exists_open_isPreconnected_superlevel_inter
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {x : M} {a : ℝ}
    (hx : f x = a) (hr : mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) :
    ∃ V : Set M, IsOpen V ∧ x ∈ V ∧ IsPreconnected (V ∩ {y | a < f y}) := by
  have hE : ¬ Subsingleton E := by
    intro hE
    let := hE
    apply hr
    change (show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) f x) = 0
    ext v
    have hv : v = 0 := Subsingleton.elim _ _
    change (show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) f x) v = 0
    rw [hv]
    exact (show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) f x).map_zero
  let : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero
    (Module.finrank_pos (R := ℝ) (M := E)).ne'
  let L : E ≃L[ℝ] MorseModel (m + 1) :=
    ContinuousLinearEquiv.ofFinrankEq (hm.trans (Module.finrank_fin_fun ℝ).symm)
  let J := I.transContinuousLinearEquiv L
  have hfJ : ContMDiff J 𝓘(ℝ, ℝ) ∞ f := L.contMDiff_transContinuousLinearEquiv_left.mpr hf
  have hrJ : mfderiv J 𝓘(ℝ, ℝ) f x ≠ 0 := fun h =>
    hr ((isCriticalPointAt_transContinuousLinearEquiv_iff I L f x).mp h)
  exact exists_open_isPreconnected_superlevel_inter_model J hfJ hx hrJ

theorem superlevel_connectedComponentIn_eq_of_mem_closure
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {x p q : M} {a : ℝ}
    (hx : f x = a) (hr : mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (hp : x ∈ closure (connectedComponentIn {y | a < f y} p))
    (hq : x ∈ closure (connectedComponentIn {y | a < f y} q)) :
    connectedComponentIn {y | a < f y} p = connectedComponentIn {y | a < f y} q := by
  obtain ⟨V, hV, hxV, hc⟩ := exists_open_isPreconnected_superlevel_inter I hf hx hr
  obtain ⟨u, huV, hu⟩ := mem_closure_iff_nhds.mp hp V (hV.mem_nhds hxV)
  obtain ⟨v, hvV, hv⟩ := mem_closure_iff_nhds.mp hq V (hV.mem_nhds hxV)
  have huS : u ∈ V ∩ {y | a < f y} := ⟨huV, connectedComponentIn_subset _ _ hu⟩
  have hvS : v ∈ V ∩ {y | a < f y} := ⟨hvV, connectedComponentIn_subset _ _ hv⟩
  exact (connectedComponentIn_eq hu).trans
    ((connectedComponentIn_eq (hc.subset_connectedComponentIn huS inter_subset_right hvS)).trans
      (connectedComponentIn_eq hv).symm)
end DifferentialGeometry.Manifold.RegularLevel
