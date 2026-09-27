import DifferentialGeometry.Bundle.Orientation.Basic
import DifferentialGeometry.Bundle.Orientation.BasisContinuity
import Mathlib.Topology.VectorBundle.Basic

noncomputable section
open Bundle Set Filter
open scoped Topology

namespace DifferentialGeometry.VectorBundle

variable {n : ℕ} {B E J X : Type*} [TopologicalSpace B] [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
attribute [local instance] orientationTopology
local instance frameTransportDiscreteTopology : DiscreteTopology (Orientation ℝ E (Fin n)) := ⟨rfl⟩

theorem isLocallyConstant_frame_orientation (Z : VectorBundleCore ℝ B E J)
    (hdim : Module.finrank ℝ E = n) (γ : X → B) (hγ : Continuous γ)
    (o : ∀ x, Orientation ℝ (Z.Fiber x) (Fin n))
    (ho : IsCompatibleOrientation (F := E) Z.Fiber o)
    (b : ∀ x, Module.Basis (Fin n) ℝ (Z.Fiber (γ x)))
    (hb : ∀ i, Continuous (fun x => (⟨γ x, b x i⟩ : Z.TotalSpace))) :
    IsLocallyConstant (fun x => (b x).orientation = o (γ x)) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  obtain ⟨t, ht, U, hUx, hU, p, hp⟩ := ho (γ x)
  let S : Set X := γ ⁻¹' t.baseSet
  have hS : IsOpen S := t.open_baseSet.preimage hγ
  have hxS : x ∈ S := hU (mem_of_mem_nhds hUx)
  let xS : S := ⟨x, hxS⟩
  let c : S → Module.Basis (Fin n) ℝ E := fun y =>
    (b y).map (t.continuousLinearEquivAt ℝ (γ y) y.property).toLinearEquiv
  have hc (i : Fin n) : Continuous (fun y : S => c y i) := by
    rw [continuous_iff_continuousAt]
    intro y
    have hbs : Continuous (fun z : S => (⟨γ z, b z i⟩ : Z.TotalSpace)) :=
      (hb i).comp continuous_subtype_val
    have hsource : (⟨γ y, b y i⟩ : Z.TotalSpace) ∈ t.source :=
      t.mem_source.mpr y.property
    have htcont : ContinuousAt (fun w : Z.TotalSpace => (t w).2) (⟨γ y, b y i⟩ : Z.TotalSpace) :=
      (t.continuousAt hsource).snd
    have hh : ContinuousAt (fun z : S => (t (⟨γ z, b z i⟩ : Z.TotalSpace)).2) y :=
      ContinuousAt.comp (f := fun z : S => (⟨γ z, b z i⟩ : Z.TotalSpace))
        (x := y) htcont (hbs.continuousAt (x := y))
    convert hh using 1
    ext z
    change t.continuousLinearEquivAt ℝ (γ z) z.property (b z i) = _
    rw [t.coe_continuousLinearEquivAt_eq (R := ℝ) z.property]
    exact Trivialization.continuousLinearMapAt_apply_of_mem ℝ t z.property _
  have hcori := continuous_basis_orientation hdim c hc
  have hsame : ∀ᶠ y in 𝓝 xS, (c y).orientation = (c xS).orientation :=
    hcori.continuousAt.eventually ((isOpen_discrete {(c xS).orientation}).mem_nhds rfl)
  have hnearU : ∀ᶠ y : S in 𝓝 xS, γ y ∈ U :=
    (hγ.comp continuous_subtype_val).continuousAt hUx
  have he (y : S) (hy : γ y ∈ U) :
      ((b y).orientation = o (γ y)) ↔ (c y).orientation = p := by
    rw [show (c y).orientation =
      Orientation.map (Fin n) (t.continuousLinearEquivAt ℝ (γ y) y.property).toLinearEquiv
        (b y).orientation from Module.Basis.orientation_map _ _]
    rw [← hp (γ y) hy]
    exact (Orientation.map (Fin n)
      (t.continuousLinearEquivAt ℝ (γ y) y.property).toLinearEquiv).injective.eq_iff.symm
  have hevent : ∀ᶠ y : S in 𝓝 xS,
      ((b y).orientation = o (γ y)) = ((b x).orientation = o (γ x)) := by
    filter_upwards [hsame, hnearU] with y hy hyU
    apply propext
    rw [he y hyU, he xS (mem_of_mem_nhds hUx), hy]
  have hh := (eventually_nhds_subtype_iff S xS
    (fun y => ((b y).orientation = o (γ y)) = ((b x).orientation = o (γ x)))).mp hevent
  rwa [nhdsWithin_eq_nhds.mpr (hS.mem_nhds hxS)] at hh

theorem frame_orientation_eq_iff [PreconnectedSpace X]
    (Z : VectorBundleCore ℝ B E J) (hdim : Module.finrank ℝ E = n)
    (γ : X → B) (hγ : Continuous γ)
    (o : ∀ x, Orientation ℝ (Z.Fiber x) (Fin n))
    (ho : IsCompatibleOrientation (F := E) Z.Fiber o)
    (b : ∀ x, Module.Basis (Fin n) ℝ (Z.Fiber (γ x)))
    (hb : ∀ i, Continuous (fun x => (⟨γ x, b x i⟩ : Z.TotalSpace))) (x y : X) :
    ((b x).orientation = o (γ x)) ↔ ((b y).orientation = o (γ y)) := by
  exact (isLocallyConstant_frame_orientation Z hdim γ hγ o ho b hb).apply_eq_of_preconnectedSpace
     x y ▸ Iff.rfl

end DifferentialGeometry.VectorBundle
