import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Boost
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Affine.MazurUlam

noncomputable section

namespace DifferentialGeometry.Hyperboloid

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

private theorem isometry_time_of_origin_fixed
    (g : Hyperboloid E ≃ᵢ Hyperboloid F) (hg : g origin = origin) (x : Hyperboloid E) :
    (g x).time = x.time := by
  have h := congrArg Real.cosh (g.dist_eq x origin)
  rw [cosh_dist, cosh_dist, hg] at h
  simpa only [origin_time, origin_space, inner_zero_right, mul_one, sub_zero] using h

private theorem isometry_inner_of_origin_fixed
    (g : Hyperboloid E ≃ᵢ Hyperboloid F) (hg : g origin = origin) (x y : Hyperboloid E) :
    inner ℝ (g x).space (g y).space = inner ℝ x.space y.space := by
  have h := congrArg Real.cosh (g.dist_eq x y)
  rw [cosh_dist, cosh_dist, isometry_time_of_origin_fixed g hg x,
    isometry_time_of_origin_fixed g hg y] at h
  linarith

private def spatialEquiv (g : Hyperboloid E ≃ᵢ Hyperboloid F) : E ≃ F :=
  (spaceEquiv (E := E)).symm.trans (g.toEquiv.trans (spaceEquiv (E := F)))

private def spatialIsometry (g : Hyperboloid E ≃ᵢ Hyperboloid F)
    (hg : g origin = origin) : E ≃ᵢ F where
  toEquiv := spatialEquiv g
  isometry_toFun := isometry_iff_dist_eq.mpr fun u v => by
    have hu := isometry_inner_of_origin_fixed g hg (ofSpace u) (ofSpace u)
    have hv := isometry_inner_of_origin_fixed g hg (ofSpace v) (ofSpace v)
    have huv := isometry_inner_of_origin_fixed g hg (ofSpace u) (ofSpace v)
    simp only [space_ofSpace, real_inner_self_eq_norm_sq] at hu hv
    simp only [space_ofSpace] at huv
    change dist (g (ofSpace u)).space (g (ofSpace v)).space = dist u v
    rw [dist_eq_norm, dist_eq_norm]
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sub_sq_real, norm_sub_sq_real, hu, hv, huv]

def spatialLorentzEquiv (L : E ≃ₗᵢ[ℝ] F) :
    (lorentzForm E).IsometryEquiv (lorentzForm F) where
  toLinearEquiv := (LinearEquiv.refl ℝ ℝ).prodCongr L.toLinearEquiv
  map_app' z w := by
    change inner ℝ (L z.2) (L w.2) - z.1 * w.1 = inner ℝ z.2 w.2 - z.1 * w.1
    rw [L.inner_map_map]

private theorem exists_lorentz_extension_of_origin_fixed
    (g : Hyperboloid E ≃ᵢ Hyperboloid F) (hg : g origin = origin) :
    ∃ A : (lorentzForm E).IsometryEquiv (lorentzForm F),
      ∀ x : Hyperboloid E, A (x.time, x.space) = ((g x).time, (g x).space) := by
  let s := spatialIsometry g hg
  have hs : s 0 = 0 := by
    change (g origin).space = 0
    rw [hg, origin_space]
  let L := s.toRealLinearIsometryEquivOfMapZero hs
  refine ⟨spatialLorentzEquiv L, ?_⟩
  intro x
  apply Prod.ext
  · exact (isometry_time_of_origin_fixed g hg x).symm
  · change (g (ofSpace x.space)).space = (g x).space
    rw [ofSpace_space]

theorem exists_unique_lorentz_extension (f : Hyperboloid E ≃ᵢ Hyperboloid F) :
    ∃! A : (lorentzForm E).IsometryEquiv (lorentzForm F),
      ∀ x : Hyperboloid E, A (x.time, x.space) = ((f x).time, (f x).space) := by
  let g := f.trans (boost (f origin)).symm
  have hg : g origin = origin := by
    change (boost (f origin)).symm (f origin) = origin
    simpa only [boost_origin] using (boost (f origin)).symm_apply_apply origin
  obtain ⟨A₀, hA₀⟩ := exists_lorentz_extension_of_origin_fixed g hg
  let A := A₀.trans (lorentzBoost (f origin))
  have hA (x : Hyperboloid E) : A (x.time, x.space) = ((f x).time, (f x).space) := by
    have hb : boost (f origin) (g x) = f x := by
      change boost (f origin) ((boost (f origin)).symm (f x)) = f x
      exact (boost (f origin)).apply_symm_apply (f x)
    change lorentzBoost (f origin) (A₀ (x.time, x.space)) = _
    rw [hA₀]
    calc
      lorentzBoost (f origin) ((g x).time, (g x).space) =
          ((boost (f origin) (g x)).time, (boost (f origin) (g x)).space) := by
        rw [lorentzBoost_apply, boost_coordinates]
      _ = ((f x).time, (f x).space) := by rw [hb]
  refine ⟨A, hA, ?_⟩
  intro C hC
  apply DFunLike.ext
  rintro ⟨t, v⟩
  have ho : C (1, 0) = A (1, 0) := by
    simpa only [origin_time, origin_space] using (hC origin).trans (hA origin).symm
  have hv : C ((ofSpace v).time, v) = A ((ofSpace v).time, v) := by
    simpa only [space_ofSpace] using (hC (ofSpace v)).trans (hA (ofSpace v)).symm
  have hd : (t, v) = (t - (ofSpace v).time) • (1, (0 : E)) + ((ofSpace v).time, v) := by
    ext <;> simp
  rw [hd, map_add, map_smul, map_add, map_smul, ho, hv]

def lorentzExtension (f : Hyperboloid E ≃ᵢ Hyperboloid F) :
    (lorentzForm E).IsometryEquiv (lorentzForm F) :=
  (exists_unique_lorentz_extension f).exists.choose

@[simp] theorem lorentzExtension_apply (f : Hyperboloid E ≃ᵢ Hyperboloid F)
    (x : Hyperboloid E) :
    lorentzExtension f (x.time, x.space) = ((f x).time, (f x).space) :=
  (exists_unique_lorentz_extension f).exists.choose_spec x

theorem lorentzExtension_origin_time_pos (f : Hyperboloid E ≃ᵢ Hyperboloid F) :
    0 < (lorentzExtension f (1, 0)).1 := by
  have h : (lorentzExtension f (1, 0)).1 = (f origin).time := by
    simpa only [origin_time, origin_space] using
      congrArg Prod.fst (lorentzExtension_apply f origin)
  rw [h]
  exact (f origin).time_pos

@[simp] theorem lorentzIsometryEquiv_lorentzExtension
    (f : Hyperboloid E ≃ᵢ Hyperboloid F) :
    lorentzIsometryEquiv (lorentzExtension f) (lorentzExtension_origin_time_pos f) = f := by
  apply IsometryEquiv.ext
  intro x
  apply Hyperboloid.ext
  exact congrArg Prod.snd ((lorentzIsometryEquiv_coordinates (lorentzExtension f)
    (lorentzExtension_origin_time_pos f) x).trans (lorentzExtension_apply f x))

@[simp] theorem lorentzExtension_refl :
    lorentzExtension (IsometryEquiv.refl (Hyperboloid E)) =
      LinearMap.BilinForm.IsometryEquiv.refl (lorentzForm E) := by
  exact (exists_unique_lorentz_extension (IsometryEquiv.refl (Hyperboloid E))).unique
    (lorentzExtension_apply _) (fun _ => rfl)

@[simp] theorem lorentzExtension_trans {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (f : Hyperboloid E ≃ᵢ Hyperboloid F) (g : Hyperboloid F ≃ᵢ Hyperboloid G) :
    lorentzExtension (f.trans g) = (lorentzExtension f).trans (lorentzExtension g) := by
  apply (exists_unique_lorentz_extension (f.trans g)).unique (lorentzExtension_apply _)
  intro x
  change lorentzExtension g (lorentzExtension f (x.time, x.space)) =
    ((g (f x)).time, (g (f x)).space)
  rw [lorentzExtension_apply, lorentzExtension_apply]

@[simp] theorem lorentzExtension_symm (f : Hyperboloid E ≃ᵢ Hyperboloid F) :
    lorentzExtension f.symm = (lorentzExtension f).symm := by
  apply (exists_unique_lorentz_extension f.symm).unique (lorentzExtension_apply _)
  intro y
  have h := congrArg (lorentzExtension f).symm (lorentzExtension_apply f (f.symm y))
  rw [f.apply_symm_apply] at h
  have hi : (lorentzExtension f).symm
      (lorentzExtension f ((f.symm y).time, (f.symm y).space)) =
        ((f.symm y).time, (f.symm y).space) :=
    (lorentzExtension f).toLinearEquiv.symm_apply_apply _
  rw [hi] at h
  exact h.symm

end DifferentialGeometry.Hyperboloid
