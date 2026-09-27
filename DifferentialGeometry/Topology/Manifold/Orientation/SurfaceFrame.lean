import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.LinearAlgebra.Orientation
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.LocallyConstant.Basic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold Set Module
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

structure SurfaceOrientation where
  orientation : (x : M) → Orientation ℝ (TangentSpace I x) (Fin 2)
  locally_constant : ∀ p x : M,
    ∀ hx : x ∈ (trivializationAt E (TangentSpace I) p).baseSet,
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∃ hU : U ⊆ (trivializationAt E (TangentSpace I) p).baseSet,
      ∀ y : M, ∀ hy : y ∈ U,
        Orientation.map (Fin 2)
            ((trivializationAt E (TangentSpace I) p).linearEquivAt ℝ y (hU hy))
            (orientation y) =
          Orientation.map (Fin 2)
            ((trivializationAt E (TangentSpace I) p).linearEquivAt ℝ x hx)
            (orientation x)

variable {I M}

private theorem continuousAt_basis_det {X : Type*} [TopologicalSpace X]
    (A : Basis (Fin 2) ℝ E) (v : X → Fin 2 → E) {a : X}
    (hv : ∀ i, ContinuousAt (fun x => v x i) a) :
    ContinuousAt (fun x => A.det (v x)) a := by
  have hmat : ContinuousAt (fun x => A.toMatrix (v x)) a := by
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    exact (continuous_apply i).continuousAt.comp
      (A.equivFunL.continuous.continuousAt.comp (hv j))
  exact (continuous_id.matrix_det).continuousAt.comp hmat

theorem SurfaceOrientation.isLocallyConstant_frame_agrees
    (o : SurfaceOrientation I M) {X : Type*} [TopologicalSpace X]
    (γ : X → M) (hγ : Continuous γ)
    (b : (x : X) → Basis (Fin 2) ℝ (TangentSpace I (γ x)))
    (hb : ∀ i : Fin 2, Continuous (fun x =>
      TotalSpace.mk' E (E := TangentSpace I) (γ x) (b x i))) :
    IsLocallyConstant (fun x => o.orientation (γ x) = (b x).orientation) := by
  classical
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro a
  let e := trivializationAt E (TangentSpace I) (γ a)
  have ha : γ a ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt _ _ _
  let ea := e.linearEquivAt ℝ (γ a) ha
  let A := (b a).map ea
  let v : X → Fin 2 → E := fun x i =>
    (e (TotalSpace.mk' E (E := TangentSpace I) (γ x) (b x i))).2
  have hv : ∀ i, ContinuousAt (fun x => v x i) a := by
    intro i
    exact ((e.continuousAt (e.mem_source.mpr ha)).comp (hb i).continuousAt).snd
  have hfa : A.det (v a) = 1 := by
    have hvA : v a = A := by
      funext i
      exact (e.linearEquivAt_apply (R := ℝ) (γ a) ha (b a i)).symm
    rw [hvA, A.det_self]
  have hpos : ∀ᶠ x in 𝓝 a, 0 < A.det (v x) :=
    (continuousAt_basis_det A v hv).eventually (Ioi_mem_nhds (by
      change 0 < A.det (v a)
      rw [hfa]
      exact zero_lt_one))
  obtain ⟨U, hUopen, haU, hU, ho⟩ := o.locally_constant (γ a) (γ a) ha
  have hnear : ∀ᶠ x in 𝓝 a, γ x ∈ U :=
    hγ.continuousAt.preimage_mem_nhds (hUopen.mem_nhds haU)
  filter_upwards [hpos, hnear] with x hx hxU
  let ex := e.linearEquivAt ℝ (γ x) (hU hxU)
  have hvB : v x = (b x).map ex := by
    funext i
    exact (e.linearEquivAt_apply (R := ℝ) (γ x) (hU hxU) (b x i)).symm
  have hAB : A.orientation = ((b x).map ex).orientation :=
    (A.orientation_eq_iff_det_pos _).mpr (hvB ▸ hx)
  have hO : Orientation.map (Fin 2) ex (o.orientation (γ x)) =
      Orientation.map (Fin 2) ea (o.orientation (γ a)) := ho (γ x) hxU
  apply propext
  constructor
  · intro hxO
    apply (Orientation.map (Fin 2) ea).injective
    calc
      Orientation.map (Fin 2) ea (o.orientation (γ a)) =
          Orientation.map (Fin 2) ex (o.orientation (γ x)) := hO.symm
      _ = Orientation.map (Fin 2) ex (b x).orientation := congrArg _ hxO
      _ = ((b x).map ex).orientation := ((b x).orientation_map ex).symm
      _ = A.orientation := hAB.symm
      _ = Orientation.map (Fin 2) ea (b a).orientation := (b a).orientation_map ea
  · intro haO
    apply (Orientation.map (Fin 2) ex).injective
    calc
      Orientation.map (Fin 2) ex (o.orientation (γ x)) =
          Orientation.map (Fin 2) ea (o.orientation (γ a)) := hO
      _ = Orientation.map (Fin 2) ea (b a).orientation := congrArg _ haO
      _ = A.orientation := ((b a).orientation_map ea).symm
      _ = ((b x).map ex).orientation := hAB
      _ = Orientation.map (Fin 2) ex (b x).orientation := (b x).orientation_map ex

theorem SurfaceOrientation.frame_orientation_eq_of_loop
    (o : SurfaceOrientation I M) {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] (γ : X → M) (hγ : Continuous γ)
    (b : (x : X) → Basis (Fin 2) ℝ (TangentSpace I (γ x)))
    (hb : ∀ i : Fin 2, Continuous (fun x =>
      TotalSpace.mk' E (E := TangentSpace I) (γ x) (b x i)))
    (a z : X) (hloop : γ a = γ z) :
    (b a).orientation = (b z).orientation := by
  have hsign := (o.isLocallyConstant_frame_agrees γ hγ b hb).apply_eq_of_preconnectedSpace a z
  have ho : o.orientation (γ a) = o.orientation (γ z) := by rw [hloop]
  by_cases ha : o.orientation (γ a) = (b a).orientation
  · have hz : o.orientation (γ z) = (b z).orientation := (Iff.of_eq hsign).mp ha
    exact ha.symm.trans (ho.trans hz)
  · have hz : o.orientation (γ z) ≠ (b z).orientation := fun hz =>
      ha ((Iff.of_eq hsign).mpr hz)
    have hna := ((b a).orientation_ne_iff_eq_neg (o.orientation (γ a))).mp ha
    have hnz := ((b z).orientation_ne_iff_eq_neg (o.orientation (γ z))).mp hz
    apply neg_injective
    exact hna.symm.trans (ho.trans hnz)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
