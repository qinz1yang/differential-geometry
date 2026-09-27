import Mathlib.Topology.Homotopy.Lifting

noncomputable section
open scoped unitInterval

namespace DifferentialGeometry.Topology.Covering

variable {E B X : Type*} [TopologicalSpace E] [TopologicalSpace B]
  [TopologicalSpace X] {p : E → B} (hp : IsCoveringMap p)

include hp

theorem discrete_fiber (b : B) : DiscreteTopology (p ⁻¹' {b}) :=
  (hp b).discreteTopology_fiber

theorem lifts_unique [PreconnectedSpace X] {f g : C(X, E)}
    (h : p ∘ f = p ∘ g) (x : X) (hx : f x = g x) : f = g :=
  DFunLike.ext' (hp.eq_of_comp_eq f.continuous g.continuous h x hx)

theorem exists_unique_path_lift (γ : C(I, B)) (e : E) (he : p e = γ 0) :
    ∃! Γ : C(I, E), p ∘ Γ = γ ∧ Γ 0 = e := by
  refine ⟨hp.liftPath γ e he.symm, ⟨hp.liftPath_lifts .., hp.liftPath_zero ..⟩, ?_⟩
  intro Γ hΓ
  exact (hp.eq_liftPath_iff' he.symm).mpr hΓ

def squareLift (H : C(I × I, B)) (h₀ : C(I, E)) (he : ∀ s, p (h₀ s) = H (s, 0)) :
    C(I × I, E) :=
  (hp.liftHomotopy (H.comp .prodSwap) h₀ (fun s => (he s).symm)).comp .prodSwap

theorem squareLift_projects (H : C(I × I, B)) (h₀ : C(I, E))
    (he : ∀ s, p (h₀ s) = H (s, 0)) : p ∘ squareLift hp H h₀ he = H := by
  funext st
  exact congrFun (hp.liftHomotopy_lifts (H.comp .prodSwap) h₀
    (fun s => (he s).symm)) st.swap

theorem squareLift_bottom (H : C(I × I, B)) (h₀ : C(I, E))
    (he : ∀ s, p (h₀ s) = H (s, 0)) (s : I) : squareLift hp H h₀ he (s, 0) = h₀ s :=
  hp.liftHomotopy_zero (H.comp .prodSwap) h₀ (fun s => (he s).symm) s

theorem exists_unique_square_lift (H : C(I × I, B)) (h₀ : C(I, E))
    (he : ∀ s, p (h₀ s) = H (s, 0)) :
    ∃! F : C(I × I, E), p ∘ F = H ∧ ∀ s, F (s, 0) = h₀ s := by
  refine ⟨squareLift hp H h₀ he,
    ⟨squareLift_projects hp H h₀ he, squareLift_bottom hp H h₀ he⟩, ?_⟩
  intro F hF
  exact lifts_unique hp (hF.1.trans (squareLift_projects hp H h₀ he).symm)
    (0, 0) ((hF.2 0).trans (squareLift_bottom hp H h₀ he 0).symm)

theorem squareLift_vertical_constant (H : C(I × I, B)) (h₀ : C(I, E))
    (he : ∀ s, p (h₀ s) = H (s, 0)) (s : I)
    (hs : ∀ t, H (s, t) = H (s, 0)) (t : I) :
    squareLift hp H h₀ he (s, t) = h₀ s := by
  have h := hp.const_of_comp
    ((squareLift hp H h₀ he).continuous.comp (Continuous.prodMk_right s))
    (fun t t' => by
      change p (squareLift hp H h₀ he (s, t)) = p (squareLift hp H h₀ he (s, t'))
      exact (congrFun (squareLift_projects hp H h₀ he) (s, t)).trans
        ((hs t).trans ((hs t').symm.trans
          (congrFun (squareLift_projects hp H h₀ he) (s, t')).symm))) t 0
  exact h.trans (squareLift_bottom hp H h₀ he s)

theorem liftPath_comp (γ : C(I, B)) (e : E) (he : γ 0 = p e) (r : C(I, I)) :
    hp.liftPath (γ.comp r) (hp.liftPath γ e he (r 0))
      (congrFun (hp.liftPath_lifts γ e he) (r 0)).symm =
      (hp.liftPath γ e he).comp r := by
  symm
  apply (hp.eq_liftPath_iff' _).mpr
  exact ⟨funext (fun t => congrFun (hp.liftPath_lifts γ e he) (r t)), rfl⟩

theorem liftPath_reverse (γ : C(I, B)) (e : E) (he : γ 0 = p e) :
    hp.liftPath (γ.comp ⟨unitInterval.symm, unitInterval.continuous_symm⟩)
      (hp.liftPath γ e he 1)
      (by simpa using (congrFun (hp.liftPath_lifts γ e he) 1).symm) =
      (hp.liftPath γ e he).comp ⟨unitInterval.symm, unitInterval.continuous_symm⟩ :=
  by simpa using liftPath_comp hp γ e he ⟨unitInterval.symm, unitInterval.continuous_symm⟩

def intervalMap (a b : I) : C(I, I) := ⟨Set.Icc.convexComb a b, Set.Icc.continuous_convexComb a b⟩

theorem liftPath_interval (γ : C(I, B)) (e : E) (he : γ 0 = p e) (a b : I) :
    hp.liftPath (γ.comp (intervalMap a b)) (hp.liftPath γ e he a)
      (by simpa [intervalMap] using (congrFun (hp.liftPath_lifts γ e he) a).symm) =
      (hp.liftPath γ e he).comp (intervalMap a b) := by
  simpa [intervalMap] using liftPath_comp hp γ e he (intervalMap a b)

theorem liftPath_constant (e : E) :
    hp.liftPath (.const I (p e)) e rfl = .const I e := hp.liftPath_const rfl

theorem liftPath_concat {x y z : B} (e : E) (he : x = p e)
    (γ : Path x y) (δ : Path y z) :
    let Γ := hp.liftPath γ e (γ.source.trans he)
    hp.liftPath (γ.trans δ) e (by simpa) =
      (⟨Γ, hp.liftPath_zero .., rfl⟩ : Path e (Γ 1)).trans
        ⟨hp.liftPath δ (Γ 1)
          (by simpa using (congrFun (hp.liftPath_lifts γ e (γ.source.trans he)) 1).symm),
          hp.liftPath_zero .., rfl⟩ :=
  hp.liftPath_trans he γ δ

theorem lifted_endpoint_eq_of_homotopicRel {γ δ : C(I, B)}
    (h : γ.HomotopicRel δ {0, 1}) (e : E) (hγ : γ 0 = p e) (hδ : δ 0 = p e) :
    hp.liftPath γ e hγ 1 = hp.liftPath δ e hδ 1 :=
  hp.liftPath_apply_one_eq_of_homotopicRel h e hγ hδ

theorem squareLift_comp (H : C(I × I, B)) (h₀ : C(I, E))
    (he : ∀ s, p (h₀ s) = H (s, 0)) (r : C(I × I, I × I)) :
    squareLift hp (H.comp r)
      ((squareLift hp H h₀ he).comp (r.comp ⟨fun s => (s, 0), by fun_prop⟩))
      (fun s => congrFun (squareLift_projects hp H h₀ he) (r (s, 0))) =
      (squareLift hp H h₀ he).comp r := by
  apply lifts_unique hp
    ((squareLift_projects hp _ _ _).trans (funext fun st =>
      (congrFun (squareLift_projects hp H h₀ he) (r st)).symm)) (0, 0)
  exact squareLift_bottom hp _ _ _ 0

theorem exists_unique_square_lift_edge (q : (I × I) ≃ₜ (I × I))
    (H : C(I × I, B)) (h : C(I, E)) (he : ∀ s, p (h s) = H (q (s, 0))) :
    ∃! F : C(I × I, E), p ∘ F = H ∧ ∀ s, F (q (s, 0)) = h s := by
  let F := (squareLift hp (H.comp ⟨q, q.continuous⟩) h he).comp ⟨q.symm, q.symm.continuous⟩
  have hproj : p ∘ F = H := by
    funext st
    simpa [F] using congrFun (squareLift_projects hp (H.comp ⟨q, q.continuous⟩) h he) (q.symm st)
  have hedge (s : I) : F (q (s, 0)) = h s := by
    simpa [F] using squareLift_bottom hp (H.comp ⟨q, q.continuous⟩) h he s
  refine ⟨F, ⟨hproj, hedge⟩, ?_⟩
  intro G hG
  exact lifts_unique hp (hG.1.trans hproj.symm) (q (0, 0))
    ((hG.2 0).trans (hedge 0).symm)

theorem squareLift_left_of_compatible (H : C(I × I, B)) (h₀ hL : C(I, E))
    (he : ∀ s, p (h₀ s) = H (s, 0)) (hLproj : ∀ t, p (hL t) = H (0, t))
    (hcorner : hL 0 = h₀ 0) (t : I) : squareLift hp H h₀ he (0, t) = hL t := by
  have h := hp.eq_of_comp_eq
    ((squareLift hp H h₀ he).continuous.comp (Continuous.prodMk_right 0)) hL.continuous
    (funext fun t => (congrFun (squareLift_projects hp H h₀ he) (0, t)).trans (hLproj t).symm)
    0 ((squareLift_bottom hp H h₀ he 0).trans hcorner.symm)
  exact congrFun h t

theorem exists_unique_square_lift_adjacent (q : (I × I) ≃ₜ (I × I))
    (H : C(I × I, B)) (h₀ hL : C(I, E))
    (he : ∀ s, p (h₀ s) = H (q (s, 0)))
    (hLproj : ∀ t, p (hL t) = H (q (0, t))) (hcorner : hL 0 = h₀ 0) :
    ∃! F : C(I × I, E), p ∘ F = H ∧
      (∀ s, F (q (s, 0)) = h₀ s) ∧ ∀ t, F (q (0, t)) = hL t := by
  obtain ⟨F, ⟨hF, hbottom⟩, huniq⟩ := exists_unique_square_lift_edge hp q H h₀ he
  refine ⟨F, ⟨hF, hbottom, ?_⟩, fun G hG => huniq G ⟨hG.1, hG.2.1⟩⟩
  have h := hp.eq_of_comp_eq
    (F.continuous.comp (q.continuous.comp (Continuous.prodMk_right 0))) hL.continuous
    (funext fun t => (congrFun hF (q (0, t))).trans (hLproj t).symm)
    0 ((hbottom 0).trans hcorner.symm)
  exact congrFun h

end DifferentialGeometry.Topology.Covering
