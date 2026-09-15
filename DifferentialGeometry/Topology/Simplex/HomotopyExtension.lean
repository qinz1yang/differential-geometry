import DifferentialGeometry.Topology.Homotopy.BallHomotopyExtension
import DifferentialGeometry.Topology.Simplex.BoundaryGluing

noncomputable section

namespace DifferentialGeometry.Simplex

variable {X : Type*} [TopologicalSpace X]

theorem exists_continuous_homotopy_extension (n : ℕ)
    (f : C(stdSimplex ℝ (Fin (n + 1)), X))
    (H : C(unitInterval × boundary (Fin (n + 1)), X))
    (hH : ∀ x : boundary (Fin (n + 1)), H (0, x) = f x.val) :
    ∃ F : C(unitInterval × stdSimplex ℝ (Fin (n + 1)), X),
      (∀ x, F (0, x) = f x) ∧
      ∀ t (x : boundary (Fin (n + 1))), F (t, x.val) = H (t, x) := by
  let e := stdSimplexNormedBoundarySphereHomeomorph
    (ContinuousLinearEquiv.refl ℝ (Fin n → ℝ))
  let b := stdSimplexNormedBallHomeomorph
    (ContinuousLinearEquiv.refl ℝ (Fin n → ℝ))
  let g : C(Metric.closedBall (0 : Fin n → ℝ) 1, X) :=
    f.comp ⟨b.symm, b.symm.continuous⟩
  let K : C(unitInterval × Metric.sphere (0 : Fin n → ℝ) 1, X) :=
    H.comp ⟨fun z => (z.1, e.symm z.2),
      continuous_fst.prodMk (e.symm.continuous.comp continuous_snd)⟩
  have hK : ∀ x : Metric.sphere (0 : Fin n → ℝ) 1,
      K (0, x) = g ⟨x.val, Metric.sphere_subset_closedBall x.property⟩ := by
    intro x
    exact hH (e.symm x)
  obtain ⟨G, hG, hside⟩ := Topology.exists_continuous_ball_homotopy_extension g K hK
  refine ⟨G.comp ⟨fun z => (z.1, b z.2),
    continuous_fst.prodMk (b.continuous.comp continuous_snd)⟩, ?_, ?_⟩
  · intro x
    change G (0, b x) = f x
    rw [hG]
    exact congrArg f (b.symm_apply_apply x)
  · intro t x
    have h := hside t (e x)
    change G (t, b x.val) = H (t, e.symm (e x)) at h
    change G (t, b x.val) = H (t, x)
    rw [e.symm_apply_apply] at h
    exact h

theorem exists_continuous_homotopy_extension_of_faces (n : ℕ)
    (f : C(stdSimplex ℝ (Fin (n + 3)), X))
    (H : Fin (n + 3) → C(unitInterval × stdSimplex ℝ (Fin (n + 2)), X))
    (hH : ∀ (i : Fin (n + 3)) (j : Fin (n + 2))
      (t : unitInterval) (p : stdSimplex ℝ (Fin (n + 1))),
      H i (t, stdSimplex.map j.succAbove p) =
        H (i.succAbove j) (t, stdSimplex.map (j.predAbove i).succAbove p))
    (h₀ : ∀ (i : Fin (n + 3)) (p : stdSimplex ℝ (Fin (n + 2))),
      H i (0, p) = f (stdSimplex.map i.succAbove p)) :
    ∃ F : C(unitInterval × stdSimplex ℝ (Fin (n + 3)), X),
      (∀ x, F (0, x) = f x) ∧
      ∀ (i : Fin (n + 3)) (t : unitInterval) (p : stdSimplex ℝ (Fin (n + 2))),
        F (t, stdSimplex.map i.succAbove p) = H i (t, p) := by
  let K (i : Fin (n + 3)) : C(stdSimplex ℝ (Fin (n + 2)), C(unitInterval, X)) :=
    ((H i).comp ContinuousMap.prodSwap).curry
  have hK : ∀ (i : Fin (n + 3)) (j : Fin (n + 2))
      (p : stdSimplex ℝ (Fin (n + 1))),
      K i (stdSimplex.map j.succAbove p) =
        K (i.succAbove j) (stdSimplex.map (j.predAbove i).succAbove p) := by
    intro i j p
    ext t
    exact hH i j t p
  let G : C(unitInterval × boundary (Fin (n + 3)), X) :=
    (boundaryDesc K hK).uncurry.comp ContinuousMap.prodSwap
  have hface (i : Fin (n + 3)) (t : unitInterval)
      (p : stdSimplex ℝ (Fin (n + 2))) :
      G (t, ⟨stdSimplex.map i.succAbove p,
        ⟨i, map_succAbove_apply_pivot i p⟩⟩) = H i (t, p) := by
    change boundaryDesc K hK ⟨stdSimplex.map i.succAbove p,
      ⟨i, map_succAbove_apply_pivot i p⟩⟩ t = H i (t, p)
    rw [boundaryDesc_face]
    rfl
  have hG : ∀ x : boundary (Fin (n + 3)), G (0, x) = f x.val := by
    intro x
    obtain ⟨i, hi⟩ := x.property
    let p := faceDelete i ⟨x.val, hi⟩
    have hp : stdSimplex.map i.succAbove p = x.val :=
      congrArg Subtype.val (faceInsert_faceDelete i ⟨x.val, hi⟩)
    have hx : (⟨stdSimplex.map i.succAbove p,
        ⟨i, map_succAbove_apply_pivot i p⟩⟩ : boundary (Fin (n + 3))) = x :=
      Subtype.ext hp
    rw [← hx, hface, h₀]
  obtain ⟨F, hF, hside⟩ := exists_continuous_homotopy_extension (n + 2) f G hG
  refine ⟨F, hF, ?_⟩
  intro i t p
  exact (hside t ⟨stdSimplex.map i.succAbove p,
    ⟨i, map_succAbove_apply_pivot i p⟩⟩).trans (hface i t p)

end DifferentialGeometry.Simplex
