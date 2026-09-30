import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedral.Maps.PiecewiseLinear
import DifferentialGeometry.Topology.PiecewiseLinear.Approximation.Perturbation.PiecewiseAffineLipschitz
import DifferentialGeometry.Topology.PiecewiseLinear.Approximation.Perturbation.SmallPerturbation
import Mathlib.Topology.Piecewise

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Geometry
open scoped _root_.Topology NNReal ContinuousMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_affine_extension_bound {s : Finset E}
    (hs : AffineIndependent ℝ ((↑) : s → E)) :
    ∃ C : ℝ≥0, ∀ (w : E → F) (δ : ℝ≥0), (∀ v ∈ s, ‖w v‖ ≤ δ) →
      ∃ A : E →ᵃ[ℝ] F, (∀ v ∈ s, A v = w v) ∧ LipschitzWith (δ * C) A := by
  classical
  choose c hc using fun i : s => exists_affineMap_of_affineIndependent hs
    (fun v : E => if v = i.1 then (1 : ℝ) else 0)
  choose L hL using fun i : s => (c i).lipschitzWith_of_finiteDimensional
  refine ⟨∑ i : s, L i, ?_⟩
  intro w δ hw
  let A : E →ᵃ[ℝ] F := ∑ i : s,
    ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight (w i)).toAffineMap.comp (c i)
  have heval (x : E) : A x = ∑ i : s, c i x • w i := by
    let ev : (E →ᵃ[ℝ] F) →+ F :=
      { toFun := fun B => B x
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    exact map_sum ev _ _
  refine ⟨A, ?_, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  · intro v hv
    rw [heval]
    have hi (i : s) : c i v = if i = ⟨v, hv⟩ then 1 else 0 := by
      rw [hc i v hv]
      simp only [Subtype.ext_iff, eq_comm]
    simp only [hi, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
  · rw [dist_eq_norm, heval, heval, ← Finset.sum_sub_distrib]
    calc
      ‖∑ i : s, (c i x • w i - c i y • w i)‖ ≤
          ∑ i : s, ‖c i x • w i - c i y • w i‖ := norm_sum_le _ _
      _ ≤ ∑ i : s, (δ : ℝ) * (L i : ℝ) * dist x y := by
        apply Finset.sum_le_sum
        intro i _
        rw [← sub_smul, norm_smul, ← dist_eq_norm]
        calc
          dist (c i x) (c i y) * ‖w i‖ ≤ ((L i : ℝ) * dist x y) * δ :=
            mul_le_mul ((hL i).dist_le_mul x y) (hw i i.2) (norm_nonneg _) (by positivity)
          _ = (δ : ℝ) * (L i : ℝ) * dist x y := by ring
      _ = ↑(δ * ∑ i : s, L i) * dist x y := by
        simp only [NNReal.coe_mul, NNReal.coe_sum, Finset.sum_mul, Finset.mul_sum]

theorem interpolateVertices_eq_affineMap (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (w : E → F) (s : K.faces) (A : E →ᵃ[ℝ] F)
    (hA : ∀ v ∈ s.1, A v = w v) (x : K.space)
    (hx : x.1 ∈ convexHull ℝ (s.1 : Set E)) : interpolateVertices K hK w x = A x.1 := by
  obtain ⟨B, hB, hf⟩ := interpolateVertices_affineOn K hK w s
  rw [hf x hx]
  apply AffineMap.eqOn_affineSpan (s := (s.1 : Set E))
    (fun v hv => (hB v hv).trans (hA v hv).symm)
  exact convexHull_subset_affineSpan _ hx

theorem exists_face_extension_bound (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) :
    ∃ C : ℝ≥0, ∀ (w : E → F) (δ : ℝ≥0), (∀ v ∈ K.vertices, ‖w v‖ ≤ δ) →
      ∃ A : K.faces → E →ᵃ[ℝ] F,
        (∀ s v, v ∈ s.1 → A s v = w v) ∧ (∀ s, LipschitzWith (δ * C) (A s)) := by
  classical
  let := hK.fintype
  choose C hC using fun s : K.faces => exists_affine_extension_bound (F := F) (K.indep s.2)
  refine ⟨Finset.univ.sup C, ?_⟩
  intro w δ hw
  have hvertices (s : K.faces) (v : E) (hv : v ∈ s.1) : v ∈ K.vertices :=
    K.down_closed s.2 (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  choose A hA hLip using fun s : K.faces => hC s w δ (fun v hv => hw v (hvertices s v hv))
  refine ⟨A, hA, fun s => LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  exact ((hLip s).dist_le_mul x y).trans (by
    gcongr
    exact_mod_cast (Finset.le_sup (f := C) (Finset.mem_univ s)))

omit [FiniteDimensional ℝ E] in
theorem affineMap_zero_on_convexHull_frontier {S T : Set E} (hS : Convex ℝ S)
    (hTS : T ⊆ S) (A : E →ᵃ[ℝ] F)
    (hzero : ∀ v ∈ T, v ∈ frontier S → A v = 0) {x : E}
    (hx : x ∈ convexHull ℝ T) (hxf : x ∈ frontier S) : A x = 0 := by
  let Z : Set E := {y | y ∈ S ∧ (y ∈ frontier S → A y = 0)}
  have hTZ : T ⊆ Z := fun y hy => ⟨hTS hy, hzero y hy⟩
  have hZ : Convex ℝ Z := by
    intro y hy z hz a b ha hb hab
    refine ⟨hS hy.1 hz.1 ha hb hab, fun hf => ?_⟩
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      simpa only [ha0, zero_smul, hb1, one_smul, zero_add] using
        hz.2 (by simpa only [ha0, zero_smul, hb1, one_smul, zero_add] using hf)
    by_cases hb0 : b = 0
    · have ha1 : a = 1 := by linarith
      simpa only [hb0, zero_smul, ha1, one_smul, add_zero] using
        hy.2 (by simpa only [hb0, zero_smul, ha1, one_smul, add_zero] using hf)
    have hseg : a • y + b • z ∈ openSegment ℝ y z :=
      ⟨a, b, lt_of_le_of_ne ha (Ne.symm ha0), lt_of_le_of_ne hb (Ne.symm hb0), hab, rfl⟩
    have hyf : y ∈ frontier S := ⟨subset_closure hy.1,
      fun hi => hf.2 (hS.openSegment_interior_self_subset_interior hi hz.1 hseg)⟩
    have hzf : z ∈ frontier S := ⟨subset_closure hz.1,
      fun hi => hf.2 (hS.openSegment_self_interior_subset_interior hy.1 hi hseg)⟩
    rw [Convex.combo_affine_apply hab, hy.2 hyf, hz.2 hzf, smul_zero, smul_zero, add_zero]
  exact (convexHull_min hTZ hZ hx).2 hxf

theorem interpolateVertices_zero_on_frontier (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (hconv : Convex ℝ K.space) (w : E → F)
    (hzero : ∀ v ∈ K.vertices, v ∈ frontier K.space → w v = 0)
    (x : K.space) (hx : x.1 ∈ frontier K.space) : interpolateVertices K hK w x = 0 := by
  obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp x.2
  obtain ⟨A, hA, hf⟩ := interpolateVertices_affineOn K hK w ⟨s, hs⟩
  rw [hf x hxs]
  apply affineMap_zero_on_convexHull_frontier hconv (K.subset_space hs) A _ hxs hx
  intro v hv hvf
  rw [hA v hv]
  exact hzero v (K.down_closed hs (Finset.singleton_subset_iff.mpr hv)
    (Finset.singleton_nonempty v)) hvf

omit [FiniteDimensional ℝ E] [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem exists_continuous_zero_extension {S : Set E} (hS : IsClosed S)
    (f : C(S, F)) (hzero : ∀ x : S, x.1 ∈ frontier S → f x = 0) :
    ∃ g : E → F, Continuous g ∧ (∀ x : S, g x = f x) ∧
      (∀ x ∉ interior S, g x = 0) := by
  classical
  let g : E → F := fun x => if hx : x ∈ S then f ⟨x, hx⟩ else 0
  have hgeq (x : S) : g x = f x := dite_eq_left x.2
  have hgOn : ContinuousOn g S := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact f.continuous.congr (fun x => (hgeq x).symm)
  have hgzero (x : E) (hx : x ∉ interior S) : g x = 0 := by
    by_cases hxS : x ∈ S
    · exact (hgeq ⟨x, hxS⟩).trans (hzero ⟨x, hxS⟩ ⟨subset_closure hxS, hx⟩)
    · exact dite_eq_right hxS
  have hcont : Continuous (S.piecewise g 0) :=
    continuous_piecewise (fun x hx => hgzero x hx.2)
      (by simpa only [hS.closure_eq] using hgOn) continuousOn_const
  have heq : S.piecewise g 0 = g := by
    funext x
    by_cases hx : x ∈ S
    · exact piecewise_eq_of_mem _ _ _ hx
    · rw [piecewise_eq_of_notMem _ _ _ hx, hgzero x (fun hi => hx (interior_subset hi))]
      rfl
  exact ⟨g, heq ▸ hcont, hgeq, hgzero⟩

theorem exists_interpolation_zero_extension_bound (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (hconv : Convex ℝ K.space) :
    ∃ C : ℝ≥0, ∀ (w : E → F) (δ : ℝ≥0),
      (∀ v ∈ K.vertices, ‖w v‖ ≤ δ) →
      (∀ v ∈ K.vertices, v ∈ frontier K.space → w v = 0) →
      ∃ U : E → F, LipschitzWith (δ * C) U ∧
        (∀ x : K.space, U x = interpolateVertices K hK w x) ∧
        (∀ x ∉ interior K.space, U x = 0) ∧ (∀ x, ‖U x‖ ≤ δ) := by
  classical
  let := hK.fintype
  obtain ⟨C, hC⟩ := exists_face_extension_bound (F := F) K hK
  refine ⟨C, ?_⟩
  intro w δ hw hzero
  obtain ⟨A, hA, hALip⟩ := hC w δ hw
  have hclosed : IsClosed K.space :=
    (hK.isCompact_biUnion (fun s _ => s.finite_toSet.isCompact_convexHull ℝ)).isClosed
  obtain ⟨U, hUcont, hUeq, hUzero⟩ := exists_continuous_zero_extension hclosed
    (interpolateVertices K hK w) (interpolateVertices_zero_on_frontier K hK hconv w hzero)
  let B : Option K.faces → E → F := fun i =>
    match i with
    | none => fun _ => 0
    | some s => A s
  have hBLip : ∀ i, LipschitzWith (δ * C) (B i) := by
    intro i
    cases i with
    | none => exact (LipschitzWith.const 0).weaken (by positivity)
    | some s => exact hALip s
  have hsel (x : E) : ∃ i, U x = B i x := by
    by_cases hx : x ∈ K.space
    · obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
      refine ⟨some ⟨s, hs⟩, (hUeq ⟨x, hx⟩).trans ?_⟩
      exact interpolateVertices_eq_affineMap K hK w ⟨s, hs⟩ (A ⟨s, hs⟩)
        (hA ⟨s, hs⟩) ⟨x, hx⟩ hxs
    · exact ⟨none, hUzero x (fun hi => hx (interior_subset hi))⟩
  refine ⟨U, lipschitzWith_of_finite_selection hUcont hBLip hsel, hUeq, hUzero, ?_⟩
  intro x
  by_cases hx : x ∈ K.space
  · rw [hUeq ⟨x, hx⟩]
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
    have hball : w '' (s : Set E) ⊆ closedBall 0 (δ : ℝ) := by
      rintro _ ⟨v, hv, rfl⟩
      apply mem_closedBall_zero_iff.mpr
      exact hw v (K.down_closed hs (Finset.singleton_subset_iff.mpr hv)
        (Finset.singleton_nonempty v))
    exact mem_closedBall_zero_iff.mp ((convexHull_min hball (convex_closedBall 0 (δ : ℝ)))
      (interpolateVertices_mem_convexHull K hK w ⟨s, hs⟩ ⟨x, hx⟩ hxs))
  · rw [hUzero x (fun hi => hx (interior_subset hi)), norm_zero]
    exact δ.coe_nonneg

theorem interpolateVertices_sub_id (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (w : E → E) (x : K.space) :
    interpolateVertices K hK (fun v => w v - v) x = interpolateVertices K hK w x - x.1 := by
  obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp x.2
  obtain ⟨A, hA, hf⟩ := interpolateVertices_affineOn K hK w ⟨s, hs⟩
  rw [hf x hxs, interpolateVertices_eq_affineMap K hK (fun v => w v - v)
    ⟨s, hs⟩ (A - AffineMap.id ℝ E) (fun v hv => by simp [hA v hv]) x hxs]
  rfl

theorem exists_vertex_perturbation_constant
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hconv : Convex ℝ K.space) :
    ∃ C : ℝ≥0, ∀ (δ : ℝ≥0), δ * C < 1 → ∀ w : E → E,
      (∀ v ∈ K.vertices, ‖w v - v‖ ≤ δ) →
      (∀ v ∈ K.vertices, v ∈ frontier K.space → w v = v) →
      ∃ H : E ≃ₜ E,
        (∀ x : K.space, H x = interpolateVertices K hK w x) ∧
        (∀ x ∉ interior K.space, H x = x) ∧ H '' K.space = K.space ∧
        (∀ x, ‖H x - x‖ ≤ δ) ∧ (∀ x, ‖H.symm x - x‖ ≤ δ) := by
  obtain ⟨C, hC⟩ := exists_interpolation_zero_extension_bound (F := E) K hK hconv
  refine ⟨C, ?_⟩
  intro δ hsmall w hw hfixed
  obtain ⟨U, hULip, hUeq, hUzero, hUnorm⟩ := hC (fun v => w v - v) δ hw
    (fun v hv hvf => by rw [hfixed v hv hvf, sub_self])
  let H : E ≃ₜ E := smallPerturbationHomeomorph U hULip hsmall
  have hHeq (x : K.space) : H x = interpolateVertices K hK w x := by
    change x.1 + U x = _
    rw [hUeq x, interpolateVertices_sub_id]
    abel
  have hHfix (x : E) (hx : x ∉ interior K.space) : H x = x :=
    smallPerturbationHomeomorph_fixed U hULip hsmall (hUzero x hx)
  have hHnorm (x : E) : ‖H x - x‖ ≤ δ := by
    rw [smallPerturbationHomeomorph_norm_sub]
    exact hUnorm x
  refine ⟨H, hHeq, hHfix, homeomorph_image_eq_of_fixed_compl H
    (fun x hx => hHfix x (fun hi => hx (interior_subset hi))), hHnorm, ?_⟩
  intro x
  simpa only [H.apply_symm_apply, norm_sub_rev] using hHnorm (H.symm x)

theorem exists_ambient_homeomorph_of_small_vertex_perturbation
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hconv : Convex ℝ K.space) :
    ∃ ε : ℝ≥0, 0 < ε ∧ ∀ w : E → E,
      (∀ v ∈ K.vertices, ‖w v - v‖ ≤ ε) →
      (∀ v ∈ K.vertices, v ∈ frontier K.space → w v = v) →
      ∃ H : E ≃ₜ E,
        (∀ x : K.space, H x = interpolateVertices K hK w x) ∧
        (∀ x ∉ interior K.space, H x = x) ∧ H '' K.space = K.space ∧
        (∀ x, ‖H x - x‖ ≤ ε) ∧ (∀ x, ‖H.symm x - x‖ ≤ ε) := by
  obtain ⟨C, hC⟩ := exists_vertex_perturbation_constant K hK hconv
  let ε : ℝ≥0 := (C + 1)⁻¹
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hsmall : ε * C < 1 := (inv_mul_lt_one₀ (by positivity : 0 < C + 1)).mpr (by simp)
  exact ⟨ε, hε, hC ε hsmall⟩

theorem interpolateVertices_eq_id_on_face (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (w : E → E) (s : K.faces)
    (hw : ∀ v ∈ s.1, w v = v) (x : K.space)
    (hx : x.1 ∈ convexHull ℝ (s.1 : Set E)) : interpolateVertices K hK w x = x.1 :=
  interpolateVertices_eq_affineMap K hK w s (AffineMap.id ℝ E)
    (fun v hv => (hw v hv).symm) x hx

end DifferentialGeometry.Topology.Engulfing
