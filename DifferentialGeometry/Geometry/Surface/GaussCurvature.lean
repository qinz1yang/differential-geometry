import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ContractedBianchi
import DifferentialGeometry.Geometry.Curvature.EinsteinMetric

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]


def gaussCurvature (g : SmoothRiemannianMetric I M) (x : M) : Real :=
  (2 : Real)⁻¹ * scalarCurv (I := I) g x


theorem gaussCurvature_def (g : SmoothRiemannianMetric I M) (x : M) :
    gaussCurvature (I := I) g x = (2 : Real)⁻¹ * scalarCurv (I := I) g x := rfl


private lemma ricciAt_add_left
    (g : SmoothRiemannianMetric I M) (x : M) (a b w : TangentSpace I x) :
    metricRicciAt (I := I) g x (vec2 (I := I) (a + b) w)
      = metricRicciAt (I := I) g x (vec2 (I := I) a w)
        + metricRicciAt (I := I) g x (vec2 (I := I) b w) := by
  have h := Tensor0SBundle.Tensor0SSpace.map_update_add
    (metricRicciAt (I := I) (M := M) g x) (vec2 (I := I) a w) 0 a b
  have e0 : Function.update (vec2 (I := I) a w) 0 (a + b) = vec2 (I := I) (a + b) w := by
    funext q; fin_cases q <;> simp [vec2, Function.update]
  have e1 : Function.update (vec2 (I := I) a w) 0 a = vec2 (I := I) a w := by
    funext q; fin_cases q <;> simp [vec2, Function.update]
  have e2 : Function.update (vec2 (I := I) a w) 0 b = vec2 (I := I) b w := by
    funext q; fin_cases q <;> simp [vec2, Function.update]
  rw [e0, e1, e2] at h
  exact h

private lemma ricciAt_smul_left
    (g : SmoothRiemannianMetric I M) (x : M) (c : Real) (a w : TangentSpace I x) :
    metricRicciAt (I := I) g x (vec2 (I := I) (c • a) w)
      = c * metricRicciAt (I := I) g x (vec2 (I := I) a w) := by
  have h := Tensor0SBundle.Tensor0SSpace.map_update_smul
    (metricRicciAt (I := I) (M := M) g x) (vec2 (I := I) a w) 0 c a
  have e0 : Function.update (vec2 (I := I) a w) 0 (c • a) = vec2 (I := I) (c • a) w := by
    funext q; fin_cases q <;> simp [vec2, Function.update]
  have e1 : Function.update (vec2 (I := I) a w) 0 a = vec2 (I := I) a w := by
    funext q; fin_cases q <;> simp [vec2, Function.update]
  rw [e0, e1] at h
  rw [h, smul_eq_mul]

private lemma ricciAt_add_right
    (g : SmoothRiemannianMetric I M) (x : M) (v a b : TangentSpace I x) :
    metricRicciAt (I := I) g x (vec2 (I := I) v (a + b))
      = metricRicciAt (I := I) g x (vec2 (I := I) v a)
        + metricRicciAt (I := I) g x (vec2 (I := I) v b) := by
  have h := Tensor0SBundle.Tensor0SSpace.map_update_add
    (metricRicciAt (I := I) (M := M) g x) (vec2 (I := I) v a) 1 a b
  have e0 : Function.update (vec2 (I := I) v a) 1 (a + b) = vec2 (I := I) v (a + b) := by
    funext q; fin_cases q <;> simp [vec2, Function.update]
  have e1 : Function.update (vec2 (I := I) v a) 1 a = vec2 (I := I) v a := by
    funext q; fin_cases q <;> simp [vec2, Function.update]
  have e2 : Function.update (vec2 (I := I) v a) 1 b = vec2 (I := I) v b := by
    funext q; fin_cases q <;> simp [vec2, Function.update]
  rw [e0, e1, e2] at h
  exact h

private lemma ricciAt_smul_right
    (g : SmoothRiemannianMetric I M) (x : M) (c : Real) (v a : TangentSpace I x) :
    metricRicciAt (I := I) g x (vec2 (I := I) v (c • a))
      = c * metricRicciAt (I := I) g x (vec2 (I := I) v a) := by
  have h := Tensor0SBundle.Tensor0SSpace.map_update_smul
    (metricRicciAt (I := I) (M := M) g x) (vec2 (I := I) v a) 1 c a
  have e0 : Function.update (vec2 (I := I) v a) 1 (c • a) = vec2 (I := I) v (c • a) := by
    funext q; fin_cases q <;> simp [vec2, Function.update]
  have e1 : Function.update (vec2 (I := I) v a) 1 a = vec2 (I := I) v a := by
    funext q; fin_cases q <;> simp [vec2, Function.update]
  rw [e0, e1] at h
  rw [h, smul_eq_mul]

private lemma exists_gON2
    (g : SmoothRiemannianMetric I M) (x : M) (hdim : Module.finrank Real E = 2) :
    ∃ bas : Module.Basis (Fin 2) Real (TangentSpace I x),
      (∀ a b : Fin 2, g.inner x (bas a) (bas b) = if a = b then 1 else 0) ∧
      (∀ v : TangentSpace I x, v = ∑ i : Fin 2, g.inner x v (bas i) • bas i) ∧
      (∀ v w : TangentSpace I x, g.inner x v w
        = ∑ i : Fin 2, g.inner x v (bas i) * g.inner x (bas i) w) := by
  classical
  let cd : InnerProductSpace.Core Real (TangentSpace I x) := g.toRiemannianMetric.toCore x
  have hc : ContinuousAt (fun v : TangentSpace I x => cd.inner v v) 0 :=
    g.toRiemannianMetric.continuousAt x
  have hbnd : Bornology.IsVonNBounded Real {v : TangentSpace I x |
      RCLike.re (cd.inner v v) < 1} :=
    g.toRiemannianMetric.isVonNBounded x
  letI nag : NormedAddCommGroup (TangentSpace I x) :=
    cd.toNormedAddCommGroupOfTopology hc hbnd
  letI ips : InnerProductSpace Real (TangentSpace I x) :=
    InnerProductSpace.ofCoreOfTopology cd hc hbnd
  have hinner_eq : ∀ u v : TangentSpace I x, (inner Real u v : Real) = g.inner x u v :=
    fun u v => rfl
  have hfr : Module.finrank Real (TangentSpace I x) = Fintype.card (Fin 2) := by
    rw [Fintype.card_fin]
    exact (show Module.finrank Real (TangentSpace I x) = Module.finrank Real E from rfl).trans hdim
  have hv0 : Orthonormal Real
      ((∅ : Set (Fin 2)).restrict (fun _ : Fin 2 => (0 : TangentSpace I x))) := by
    rw [orthonormal_iff_ite]
    intro i j
    exact i.2.elim
  obtain ⟨bu, -⟩ := hv0.exists_orthonormalBasis_extension_of_card_eq hfr
  refine ⟨bu.toBasis, ?_, ?_, ?_⟩
  · intro a b
    rw [OrthonormalBasis.coe_toBasis, ← hinner_eq (bu a) (bu b)]
    exact bu.inner_eq_ite a b
  · intro v
    refine (bu.sum_repr' v).symm.trans ?_
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [OrthonormalBasis.coe_toBasis]
    congr 1
    rw [g.symm x v (bu i)]
    exact hinner_eq (bu i) v
  · intro v w
    rw [← hinner_eq v w, ← bu.sum_inner_mul_inner v w]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [OrthonormalBasis.coe_toBasis, hinner_eq v (bu i), hinner_eq (bu i) w]

private lemma metricRicci_orthobasis_rm04_sum
    (g : SmoothRiemannianMetric I M) (x : M)
    (bas : Module.Basis (Fin 2) Real (TangentSpace I x))
    (hON : ∀ a b : Fin 2, g.inner x (bas a) (bas b) = if a = b then 1 else 0)
    (i j : Fin 2) :
    metricRicciAt (I := I) g x (vec2 (I := I) (bas i) (bas j))
      = ∑ a : Fin 2, metricRm04 (I := I) (M := M) g x
          (vec4 (I := I) (bas a) (bas i) (bas j) (bas a)) := by
  have hLower := rm04LowersRm13At_of_realizes (I := I) g (metricCov (I := I) (M := M) g)
    (metricRm13 (I := I) (M := M) g) (metricRm04 (I := I) (M := M) g)
    (metricCurvData (I := I) (M := M) g).h_rm13 (metricCurvData (I := I) (M := M) g).h_rm04 x
  have h := ricci_diag_eq_sum_rm04_diag_of_orthonormal (I := I) (M := M) g bas
    (metricRicci (I := I) (M := M) g) (metricRm13 (I := I) (M := M) g)
    (metricRm04 (I := I) (M := M) g)
    (metricCurvData (I := I) (M := M) g).h_ricci13 hLower hON i j
  rw [metricRicci_apply] at h
  exact h

theorem ricci_eq_gaussCurvature_smul_metric_twoDim
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    metricRicciAt (I := I) (M := M) g x (vec2 (I := I) v w) =
      gaussCurvature (I := I) g x * g.inner x v w := by
  classical
  obtain ⟨bas, hON, hexp, hpars⟩ := exists_gON2 (I := I) g x hdim
  have hinput := rm04InputSkewAt_of_leviCivita_realizes (I := I) g
    (metricRm04 (I := I) (M := M) g) (metricCurvData (I := I) (M := M) g).h_rm04 (x := x)
  have houtput := rm04OutputSkewAt_of_leviCivita_realizes (I := I) g
    (metricRm04 (I := I) (M := M) g) (metricCurvData (I := I) (M := M) g).h_rm04 (x := x)
  have hpair := rm04PairSymmAt_of_leviCivita_realizes (I := I) g
    (metricRm04 (I := I) (M := M) g) (metricCurvData (I := I) (M := M) g).h_rm04 (x := x)
  have z00 : metricRm04 (I := I) (M := M) g x
      (vec4 (I := I) (bas 0) (bas 0) (bas 0) (bas 0)) = 0 := by
    have h := hinput (bas 0) (bas 0) (bas 0) (bas 0); linarith
  have z11 : metricRm04 (I := I) (M := M) g x
      (vec4 (I := I) (bas 1) (bas 1) (bas 1) (bas 1)) = 0 := by
    have h := hinput (bas 1) (bas 1) (bas 1) (bas 1); linarith
  have z010 : metricRm04 (I := I) (M := M) g x
      (vec4 (I := I) (bas 0) (bas 0) (bas 1) (bas 0)) = 0 := by
    have h := hinput (bas 0) (bas 0) (bas 1) (bas 0); linarith
  have z011 : metricRm04 (I := I) (M := M) g x
      (vec4 (I := I) (bas 1) (bas 0) (bas 1) (bas 1)) = 0 := by
    have h := houtput (bas 1) (bas 0) (bas 1) (bas 1); linarith
  have z100 : metricRm04 (I := I) (M := M) g x
      (vec4 (I := I) (bas 0) (bas 1) (bas 0) (bas 0)) = 0 := by
    have h := houtput (bas 0) (bas 1) (bas 0) (bas 0); linarith
  have z101 : metricRm04 (I := I) (M := M) g x
      (vec4 (I := I) (bas 1) (bas 1) (bas 0) (bas 1)) = 0 := by
    have h := hinput (bas 1) (bas 1) (bas 0) (bas 1); linarith
  obtain ⟨κ, h00, h11, h01, h10⟩ : ∃ κ : Real,
      metricRicciAt (I := I) g x (vec2 (I := I) (bas 0) (bas 0)) = κ ∧
      metricRicciAt (I := I) g x (vec2 (I := I) (bas 1) (bas 1)) = κ ∧
      metricRicciAt (I := I) g x (vec2 (I := I) (bas 0) (bas 1)) = 0 ∧
      metricRicciAt (I := I) g x (vec2 (I := I) (bas 1) (bas 0)) = 0 := by
    refine ⟨metricRm04 (I := I) (M := M) g x
      (vec4 (I := I) (bas 1) (bas 0) (bas 0) (bas 1)), ?_, ?_, ?_, ?_⟩
    · rw [metricRicci_orthobasis_rm04_sum (I := I) g x bas hON 0 0, Fin.sum_univ_two,
          z00, zero_add]
    · rw [metricRicci_orthobasis_rm04_sum (I := I) g x bas hON 1 1, Fin.sum_univ_two,
          z11, add_zero, hpair (bas 0) (bas 1) (bas 1) (bas 0)]
    · rw [metricRicci_orthobasis_rm04_sum (I := I) g x bas hON 0 1, Fin.sum_univ_two,
          z010, z011, add_zero]
    · rw [metricRicci_orthobasis_rm04_sum (I := I) g x bas hON 1 0, Fin.sum_univ_two,
          z100, z101, add_zero]
  have main1 : ∀ v w : TangentSpace I x,
      metricRicciAt (I := I) g x (vec2 (I := I) v w) = κ * g.inner x v w := by
    intro v w
    obtain ⟨c0, c1, d0, d1, hv, hw, hg⟩ : ∃ c0 c1 d0 d1 : Real,
        v = c0 • bas 0 + c1 • bas 1 ∧ w = d0 • bas 0 + d1 • bas 1 ∧
        g.inner x v w = c0 * d0 + c1 * d1 := by
      refine ⟨g.inner x v (bas 0), g.inner x v (bas 1), g.inner x w (bas 0),
        g.inner x w (bas 1), ?_, ?_, ?_⟩
      · have h := hexp v; rwa [Fin.sum_univ_two] at h
      · have h := hexp w; rwa [Fin.sum_univ_two] at h
      · have h := hpars v w; rw [Fin.sum_univ_two] at h
        rw [h, g.symm x (bas 0) w, g.symm x (bas 1) w]
    rw [hg, hv, hw, ricciAt_add_left, ricciAt_smul_left, ricciAt_smul_left,
        ricciAt_add_right, ricciAt_smul_right, ricciAt_smul_right,
        ricciAt_add_right, ricciAt_smul_right, ricciAt_smul_right,
        h00, h01, h10, h11]
    ring
  have hterm : ∀ i : Fin (Module.finrank Real E),
      ricciTensor (I := I) g x (smoothOrthoFrame (I := I) g x i x)
          (smoothOrthoFrame (I := I) g x i x) = κ := by
    intro i
    rw [← DifferentialGeometry.metricRicciAt_apply_eq_ricciTensor (I := I) g x
          (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x i x),
        main1 (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x i x),
        smoothOrthoFrame_orthonormal_center (I := I) g x i i]
    simp
  have hscalar : scalarCurv (I := I) g x = 2 * κ := by
    have hsc : scalarCurv (I := I) g x = ∑ _i : Fin (Module.finrank Real E), κ := by
      unfold scalarCurv
      exact Finset.sum_congr rfl (fun i _ => hterm i)
    rw [hsc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hdim]
    norm_num
  rw [main1 v w, gaussCurvature_def, hscalar]
  ring


theorem gaussCurvature_contMDiff (g : SmoothRiemannianMetric I M) :
    ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (gaussCurvature (I := I) (M := M) g) := by
  have hfun : gaussCurvature (I := I) (M := M) g
      = fun x : M => (2 : Real)⁻¹ * metricScalarAt (I := I) (M := M) g x := by
    funext x
    rw [gaussCurvature_def, metricScalar_eq_scal (I := I) (M := M) g x]
  rw [hfun]
  exact (contMDiff_const (c := (2 : Real)⁻¹)).mul
    (metricScalar_smooth (I := I) (M := M) g)


end DifferentialGeometry.Integral.Connection
