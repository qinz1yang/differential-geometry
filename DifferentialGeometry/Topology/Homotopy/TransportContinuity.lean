import DifferentialGeometry.Topology.Homotopy.CubePathExtension
import DifferentialGeometry.Topology.Homotopy.Map



noncomputable section

open Set Function ContinuousMap
open scoped Topology

namespace DifferentialGeometry.Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x y : X}



theorem continuous_cubePathExtension_joint (n : ℕ) :
    Continuous (fun z : (Path x y × GenLoop (Fin (n + 1)) X x) ×
      (unitInterval × (Fin (n + 1) → unitInterval)) =>
        cubePathExtension n z.1.1 z.1.2 z.2) := by
  apply Continuous.if
  · intro z hz
    have heq := frontier_le_subset_eq
      ((continuous_cubeRadius n).comp (continuous_snd.comp continuous_snd))
      (continuous_const.sub
        ((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).div_const 2)) hz
    exact cubePathExtension_interface n z.1.1 z.1.2 z.2 heq
  · exact continuous_eval.comp
      ((continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).prodMk
        ((continuous_cubePrismRetract n).snd.comp continuous_snd))
  · exact (Path.continuous_uncurry_iff.mpr continuous_id).comp
      ((continuous_fst.comp continuous_fst).prodMk
        ((continuous_cubePrismRetract n).fst.comp continuous_snd))


theorem continuous_genLoopTransport (n : ℕ) :
    Continuous (fun z : Path x y × GenLoop (Fin (n + 1)) X x => genLoopTransport n z.1 z.2) := by
  apply Continuous.subtype_mk
  apply continuous_of_continuous_uncurry
  change Continuous (fun z : (Path x y × GenLoop (Fin (n + 1)) X x) ×
    (Fin (n + 1) → unitInterval) => cubePathExtension n z.1.1 z.1.2 (1, z.2))
  apply Continuous.if
  · intro z hz
    have heq := frontier_le_subset_eq ((continuous_cubeRadius n).comp continuous_snd)
      (continuous_const (y := (1 - (1 : ℝ) / 2))) hz
    exact cubePathExtension_interface n z.1.1 z.1.2 (1, z.2) heq
  · exact continuous_eval.comp
      ((continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).prodMk
        ((continuous_cubePrismRetract n).snd.comp (continuous_const.prodMk continuous_snd)))
  · exact (Path.continuous_uncurry_iff.mpr continuous_id).comp
      ((continuous_fst.comp continuous_fst).prodMk
        ((continuous_cubePrismRetract n).fst.comp (continuous_const.prodMk continuous_snd)))


theorem genLoopTransport_homotopic (n : ℕ) (p : Path x y)
    {Γ Δ : GenLoop (Fin (n + 1)) X x} (h : GenLoop.Homotopic Γ Δ) :
    GenLoop.Homotopic (genLoopTransport n p Γ) (genLoopTransport n p Δ) := by
  apply (genLoop_homotopic_iff_joined _ _).mpr
  exact ((genLoop_homotopic_iff_joined Γ Δ).mp h).map
    ((continuous_genLoopTransport n).comp (continuous_const.prodMk continuous_id))



theorem genLoopTransport_path_homotopic (n : ℕ) {p q : Path x y}
    (h : p.Homotopic q) (Γ : GenLoop (Fin (n + 1)) X x) :
    GenLoop.Homotopic (genLoopTransport n p Γ) (genLoopTransport n q Γ) := by
  obtain ⟨H⟩ := h
  let P : Path p q :=
    ⟨⟨H.eval, Path.continuous_uncurry_iff.mp H.continuous⟩, H.eval_zero, H.eval_one⟩
  have hj : Joined p q := ⟨P⟩
  exact (genLoop_homotopic_iff_joined _ _).mpr
    (hj.map ((continuous_genLoopTransport n).comp (continuous_id.prodMk continuous_const)))


theorem genLoopTransport_natural (n : ℕ) (f : C(X, Y)) (p : Path x y)
    (Γ : GenLoop (Fin (n + 1)) X x) :
    genLoopTransport n (p.map f.continuous) (genLoopPostcompose f x Γ) =
      genLoopPostcompose f y (genLoopTransport n p Γ) := by
  ext v
  change cubePathExtension n (p.map f.continuous) (genLoopPostcompose f x Γ) (1, v) =
    f (cubePathExtension n p Γ (1, v))
  unfold cubePathExtension
  split_ifs <;> rfl

end DifferentialGeometry.Topology
