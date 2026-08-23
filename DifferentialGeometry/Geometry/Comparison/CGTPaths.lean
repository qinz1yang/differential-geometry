import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Topology.Homotopy.Path

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped ENNReal Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace CGT

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [∀ x : M, ENorm (TangentSpace I x)]

noncomputable def pathLen {x y : M} (γ : Path x y) : ENNReal :=
  Manifold.pathELength I γ.extend 0 1

structure IsFlatC1Path {x y : M} (p : Path x y) : Prop where
  c1 : ContMDiff 𝓘(Real, Real) I 1 p.extend
  flat_zero : p.extend =ᶠ[𝓝 0] (fun _ : Real => x)
  flat_one : p.extend =ᶠ[𝓝 1] (fun _ : Real => y)

namespace IsFlatC1Path

variable {x y z : M} {p : Path x y} {q : Path y z}

omit [∀ x : M, ENorm (TangentSpace I x)] in
theorem refl (x : M) : IsFlatC1Path (I := I) (Path.refl x) where
  c1 := by
    simpa only [Path.refl_extend] using
      (contMDiff_const : ContMDiff 𝓘(Real, Real) I 1 (fun _ : Real => x))
  flat_zero := Filter.Eventually.of_forall fun _ => rfl
  flat_one := Filter.Eventually.of_forall fun _ => rfl

omit [∀ x : M, ENorm (TangentSpace I x)] in
theorem symm (hp : IsFlatC1Path (I := I) p) :
    IsFlatC1Path (I := I) p.symm where
  c1 := by
    rw [Path.extend_symm]
    apply hp.c1.comp
    rw [contMDiff_iff_contDiff]
    fun_prop
  flat_zero := by
    rw [Path.extend_symm]
    have hsub : Continuous (fun t : Real => 1 - t) :=
      continuous_const.sub continuous_id
    simpa only [Function.comp_apply, sub_zero] using
      hp.flat_one.comp_tendsto (by
        simpa only [sub_zero] using hsub.tendsto (0 : Real) :
        Tendsto (fun t : Real => 1 - t) (𝓝 0) (𝓝 1))
  flat_one := by
    rw [Path.extend_symm]
    have hsub : Continuous (fun t : Real => 1 - t) :=
      continuous_const.sub continuous_id
    simpa only [Function.comp_apply, sub_self] using
      hp.flat_zero.comp_tendsto (by
        simpa only [sub_self] using hsub.tendsto (1 : Real) :
        Tendsto (fun t : Real => 1 - t) (𝓝 1) (𝓝 0))

omit [∀ x : M, ENorm (TangentSpace I x)] in
theorem trans
    (hp : IsFlatC1Path (I := I) p)
    (hq : IsFlatC1Path (I := I) q) :
    IsFlatC1Path (I := I) (p.trans q) := by
  let f : Real → M := fun t => p.extend (2 * t)
  let g : Real → M := fun t => q.extend (2 * t - 1)
  have hf : ContMDiff 𝓘(Real, Real) I 1 f := by
    apply hp.c1.comp
    rw [contMDiff_iff_contDiff]
    fun_prop
  have hg : ContMDiff 𝓘(Real, Real) I 1 g := by
    apply hq.c1.comp
    rw [contMDiff_iff_contDiff]
    fun_prop
  have hmul : Continuous (fun t : Real => 2 * t) :=
    continuous_const.mul continuous_id
  have hsub : Continuous (fun t : Real => 2 * t - 1) :=
    hmul.sub continuous_const
  have h2half :
      Tendsto (fun t : Real => 2 * t) (𝓝 (1 / 2)) (𝓝 1) := by
    convert hmul.tendsto (1 / 2 : Real) using 1; norm_num
  have h2half' :
      Tendsto (fun t : Real => 2 * t - 1) (𝓝 (1 / 2)) (𝓝 0) := by
    convert hsub.tendsto (1 / 2 : Real) using 1; norm_num
  have hpf : f =ᶠ[𝓝 (1 / 2)] (fun _ : Real => y) := by
    simpa only [f, Function.comp_apply] using
      hp.flat_one.comp_tendsto h2half
  have hqg : g =ᶠ[𝓝 (1 / 2)] (fun _ : Real => y) := by
    simpa only [g, Function.comp_apply] using
      hq.flat_zero.comp_tendsto h2half'
  have hext :
      (p.trans q).extend =
        Set.piecewise (Set.Iic (1 / 2)) f g := by
    funext t
    by_cases ht : t ≤ 1 / 2
    · rw [Path.extend_trans_of_le_half p q ht]
      simp only [Set.piecewise, Set.mem_Iic, ht, ↓reduceIte, f]
    · have hhalf : 1 / 2 ≤ t := (not_le.mp ht).le
      rw [Path.extend_trans_of_half_le p q hhalf]
      simp only [Set.piecewise, Set.mem_Iic, ht, ↓reduceIte, g]
  refine {
    c1 := ?_
    flat_zero := ?_
    flat_one := ?_ }
  · rw [hext]
    exact ContMDiff.piecewise_Iic hf hg (hpf.trans hqg.symm)
  · have ht0 :
        Tendsto (fun t : Real => 2 * t) (𝓝 0) (𝓝 0) := by
      simpa only [mul_zero] using hmul.tendsto (0 : Real)
    have hp0 : f =ᶠ[𝓝 0] (fun _ : Real => x) := by
      simpa only [f, Function.comp_apply] using
        hp.flat_zero.comp_tendsto ht0
    filter_upwards
      [hp0, eventually_le_nhds (show (0 : Real) < 1 / 2 by norm_num)]
      with t hpt ht
    rw [Path.extend_trans_of_le_half p q ht]
    exact hpt
  · have ht1 :
        Tendsto (fun t : Real => 2 * t - 1) (𝓝 1) (𝓝 1) := by
      convert hsub.tendsto (1 : Real) using 1; norm_num
    have hq1 : g =ᶠ[𝓝 1] (fun _ : Real => z) := by
      simpa only [g, Function.comp_apply] using
        hq.flat_one.comp_tendsto ht1
    filter_upwards
      [hq1, eventually_ge_nhds (show (1 / 2 : Real) < 1 by norm_num)]
      with t hqt ht
    rw [Path.extend_trans_of_half_le p q ht]
    exact hqt

end IsFlatC1Path

@[simp]
theorem pathLen_refl
    [∀ z : M, ENormSMulClass Real (TangentSpace I z)]
    (x : M) :
    pathLen (I := I) (Path.refl x) = 0 := by
  rw [pathLen, Path.refl_extend,
    Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  change
    ∫⁻ _ : Real in Set.Icc 0 1,
      ‖(mfderiv 𝓘(Real, Real) I (fun _ : Real => x) _) 1‖ₑ = 0
  have hzero : ‖(0 : TangentSpace I x)‖ₑ = 0 := by
    calc
      _ = ‖(0 : Real) • (0 : TangentSpace I x)‖ₑ := by rw [zero_smul]
      _ = ‖(0 : Real)‖ₑ * ‖(0 : TangentSpace I x)‖ₑ := enorm_smul _ _
      _ = 0 := by simp
  simp only [mfderiv_const, ContinuousLinearMap.zero_apply, hzero,
    MeasureTheory.lintegral_zero]

section PathLength

variable [∀ z : M, ENormSMulClass Real (TangentSpace I z)]

theorem pathLen_symm {x y : M} {p : Path x y}
    (hp : IsFlatC1Path (I := I) p) :
    pathLen (I := I) p.symm = pathLen (I := I) p := by
  rw [pathLen, Path.extend_symm]
  simpa only [Function.comp_def, sub_self, sub_zero] using
    (Manifold.pathELength_comp_of_antitoneOn
      (I := I) (γ := p.extend)
      (f := fun t : Real => 1 - t)
      (a := 0) (b := 1) zero_le_one
      (by
        intro a _ b _ hab
        dsimp
        linarith)
      (by fun_prop)
      (by
        simpa using
          hp.c1.contMDiffOn.mdifferentiableOn one_ne_zero))

theorem pathLen_trans {x y z : M}
    {p : Path x y} {q : Path y z}
    (hp : IsFlatC1Path (I := I) p)
    (hq : IsFlatC1Path (I := I) q) :
    pathLen (I := I) (p.trans q) =
      pathLen (I := I) p + pathLen (I := I) q := by
  have hleft :
      Manifold.pathELength I (p.trans q).extend 0 (1 / 2) =
        Manifold.pathELength I p.extend 0 1 := by
    calc
      _ = Manifold.pathELength I
          (p.extend ∘ fun t : Real => 2 * t) 0 (1 / 2) := by
        apply Manifold.pathELength_congr
        intro t ht
        simpa only [Function.comp_apply] using
          Path.extend_trans_of_le_half p q ht.2
      _ = _ := by
        convert Manifold.pathELength_comp_of_monotoneOn
          (I := I) (γ := p.extend)
          (f := fun t : Real => 2 * t)
          (a := 0) (b := 1 / 2)
          (by norm_num)
          (by
            intro a _ b _ hab
            dsimp
            linarith)
          (by fun_prop)
          (by
            simpa using
              hp.c1.contMDiffOn.mdifferentiableOn one_ne_zero)
          using 1; norm_num
  have hright :
      Manifold.pathELength I (p.trans q).extend (1 / 2) 1 =
        Manifold.pathELength I q.extend 0 1 := by
    calc
      _ = Manifold.pathELength I
          (q.extend ∘ fun t : Real => 2 * t - 1) (1 / 2) 1 := by
        apply Manifold.pathELength_congr
        intro t ht
        simpa only [Function.comp_apply] using
          Path.extend_trans_of_half_le p q ht.1
      _ = _ := by
        convert Manifold.pathELength_comp_of_monotoneOn
          (I := I) (γ := q.extend)
          (f := fun t : Real => 2 * t - 1)
          (a := 1 / 2) (b := 1)
          (by norm_num)
          (by
            intro a _ b _ hab
            dsimp
            linarith)
          (by fun_prop)
          (by
            simpa using
              hq.c1.contMDiffOn.mdifferentiableOn one_ne_zero)
          using 1; norm_num
  change
    Manifold.pathELength I (p.trans q).extend 0 1 =
      Manifold.pathELength I p.extend 0 1 +
        Manifold.pathELength I q.extend 0 1
  calc
    _ = Manifold.pathELength I (p.trans q).extend 0 (1 / 2) +
        Manifold.pathELength I (p.trans q).extend (1 / 2) 1 :=
      (Manifold.pathELength_add
        (I := I) (γ := (p.trans q).extend)
        (by norm_num) (by norm_num)).symm
    _ = _ := by rw [hleft, hright]

end PathLength

section FlatPath

variable [∀ z : M, ENormSMulClass Real (TangentSpace I z)]

theorem exists_flat_path
    {x y : M} {r : ENNReal}
    (hxy : Manifold.riemannianEDist I x y < r) :
    ∃ p : Path x y,
      IsFlatC1Path (I := I) p ∧
      pathLen (I := I) p < r := by
  obtain ⟨γ, hγ0, hγ1, hγC1, hγlen, hγflat0, hγflat1⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt
      hxy (a := (0 : Real)) (b := (1 : Real)) zero_lt_one
  let p : Path x y := {
    toFun := fun t => γ t
    continuous_toFun := hγC1.continuous.comp continuous_subtype_val
    source' := hγ0
    target' := hγ1 }
  let tail : Real → M :=
    Set.piecewise (Set.Iic (1 : Real)) γ (fun _ => y)
  have htailC1 : ContMDiff 𝓘(Real, Real) I 1 tail := by
    exact ContMDiff.piecewise_Iic hγC1 contMDiff_const hγflat1
  have htail0 :
      tail =ᶠ[𝓝 (0 : Real)] γ := by
    filter_upwards [eventually_lt_nhds zero_lt_one] with t ht
    exact (Set.Iic (1 : Real)).piecewise_eq_of_mem γ (fun _ => y) ht.le
  have hjoin0 :
      (fun _ : Real => x) =ᶠ[𝓝 (0 : Real)] tail :=
    hγflat0.symm.trans htail0.symm
  have hext :
      p.extend =
        Set.piecewise (Set.Iic (0 : Real)) (fun _ => x) tail := by
    funext t
    by_cases ht0 : t ≤ 0
    · rw [p.extend_of_le_zero ht0]
      exact ((Set.Iic (0 : Real)).piecewise_eq_of_mem
        (fun _ => x) tail ht0).symm
    · have h0t : 0 ≤ t := (not_le.mp ht0).le
      rw [(Set.Iic (0 : Real)).piecewise_eq_of_notMem
        (fun _ => x) tail ht0]
      by_cases ht1 : t ≤ 1
      · have ht : t ∈ Set.Icc (0 : Real) 1 := ⟨h0t, ht1⟩
        rw [p.extend_apply ht]
        change γ t = tail t
        exact ((Set.Iic (1 : Real)).piecewise_eq_of_mem
          γ (fun _ => y) ht1).symm
      · have h1t : 1 ≤ t := (not_le.mp ht1).le
        rw [p.extend_of_one_le h1t]
        exact ((Set.Iic (1 : Real)).piecewise_eq_of_notMem
          γ (fun _ => y) ht1).symm
  have hpflat0 :
      p.extend =ᶠ[𝓝 (0 : Real)] (fun _ => x) := by
    rw [hext]
    filter_upwards [hjoin0, eventually_lt_nhds zero_lt_one] with t hjoin ht
    by_cases ht0 : t ≤ 0
    · exact (Set.Iic (0 : Real)).piecewise_eq_of_mem
        (fun _ => x) tail ht0
    · rw [(Set.Iic (0 : Real)).piecewise_eq_of_notMem
        (fun _ => x) tail ht0]
      exact hjoin.symm
  have hpflat1 :
      p.extend =ᶠ[𝓝 (1 : Real)] (fun _ => y) := by
    rw [hext]
    filter_upwards [hγflat1, eventually_gt_nhds zero_lt_one] with t hγt ht
    have ht0 : ¬ t ≤ 0 := not_le.mpr ht
    rw [(Set.Iic (0 : Real)).piecewise_eq_of_notMem
      (fun _ => x) tail ht0]
    by_cases ht1 : t ≤ 1
    · change Set.piecewise (Set.Iic (1 : Real)) γ (fun _ => y) t = y
      rw [(Set.Iic (1 : Real)).piecewise_eq_of_mem
        γ (fun _ => y) ht1]
      exact hγt
    · change Set.piecewise (Set.Iic (1 : Real)) γ (fun _ => y) t = y
      exact (Set.Iic (1 : Real)).piecewise_eq_of_notMem
        γ (fun _ => y) ht1
  refine ⟨p, {
    c1 := ?_
    flat_zero := hpflat0
    flat_one := hpflat1 }, ?_⟩
  · rw [hext]
    exact ContMDiff.piecewise_Iic contMDiff_const htailC1 hjoin0
  · change Manifold.pathELength I p.extend 0 1 < r
    calc
      Manifold.pathELength I p.extend 0 1 =
          Manifold.pathELength I γ 0 1 := by
        apply Manifold.pathELength_congr
        intro t ht
        rw [p.extend_apply ht]
        rfl
      _ < r := hγlen

end FlatPath

structure ShortHomotopy (L : ENNReal) {x y : M} (p q : Path x y) where
  hom : p.Homotopy q
  flat : ∀ t : unitInterval, IsFlatC1Path (I := I) (hom.eval t)
  length_le : ∀ t : unitInterval, pathLen (I := I) (hom.eval t) ≤ L

def ShortHomotopic (L : ENNReal) {x y : M} (p q : Path x y) : Prop :=
  Nonempty (ShortHomotopy (I := I) L p q)

namespace ShortHomotopy

variable [IsManifold I 1 M]
variable [∀ z : M, ENormSMulClass Real (TangentSpace I z)]
variable {L : ENNReal} {x y : M} {p q r : Path x y}

noncomputable def mono {L' : ENNReal}
    (F : ShortHomotopy (I := I) L p q) (hLL' : L ≤ L') :
    ShortHomotopy (I := I) L' p q where
  hom := F.hom
  flat := F.flat
  length_le t := (F.length_le t).trans hLL'

noncomputable def refl
    (hpC1 : IsFlatC1Path (I := I) p)
    (hp : pathLen (I := I) p ≤ L) :
    ShortHomotopy (I := I) L p p where
  hom := Path.Homotopy.refl p
  flat t := by
    simpa only [Path.Homotopy.eval, Path.Homotopy.refl_apply] using hpC1
  length_le t := by
    simpa only [Path.Homotopy.eval, Path.Homotopy.refl_apply] using hp

noncomputable def symm (F : ShortHomotopy (I := I) L p q) :
    ShortHomotopy (I := I) L q p where
  hom := F.hom.symm
  flat t := by
    simpa only [Path.Homotopy.eval, Path.Homotopy.symm_apply] using
      F.flat (unitInterval.symm t)
  length_le t := by
    simpa only [Path.Homotopy.eval, Path.Homotopy.symm_apply] using
      F.length_le (unitInterval.symm t)

noncomputable def trans
    (F : ShortHomotopy (I := I) L p q)
    (G : ShortHomotopy (I := I) L q r) :
    ShortHomotopy (I := I) L p r where
  hom := F.hom.trans G.hom
  flat t := by
    by_cases ht : (t : Real) ≤ 1 / 2
    · let t' : unitInterval :=
        ⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩
      have h := F.flat t'
      convert h using 1
      ext s
      change (F.hom.trans G.hom) (t, s) = F.hom (t', s)
      rw [Path.Homotopy.trans_apply]
      simp only [ht, ↓reduceDIte, t']
    · let t' : unitInterval :=
        ⟨2 * t - 1,
          unitInterval.two_mul_sub_one_mem_iff.2
            ⟨(not_le.1 ht).le, t.2.2⟩⟩
      have h := G.flat t'
      convert h using 1
      ext s
      change (F.hom.trans G.hom) (t, s) = G.hom (t', s)
      rw [Path.Homotopy.trans_apply]
      simp only [ht, ↓reduceDIte, t']
  length_le t := by
    by_cases ht : (t : Real) ≤ 1 / 2
    · let t' : unitInterval :=
        ⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩
      have h := F.length_le t'
      convert h using 1
      apply congrArg (pathLen (I := I))
      ext s
      change (F.hom.trans G.hom) (t, s) = F.hom (t', s)
      rw [Path.Homotopy.trans_apply]
      simp only [ht, ↓reduceDIte, t']
    · let t' : unitInterval :=
        ⟨2 * t - 1,
          unitInterval.two_mul_sub_one_mem_iff.2
            ⟨(not_le.1 ht).le, t.2.2⟩⟩
      have h := G.length_le t'
      convert h using 1
      apply congrArg (pathLen (I := I))
      ext s
      change (F.hom.trans G.hom) (t, s) = G.hom (t', s)
      rw [Path.Homotopy.trans_apply]
      simp only [ht, ↓reduceDIte, t']

omit [IsManifold I 1 M]
    [∀ z : M, ENormSMulClass Real (TangentSpace I z)] in
private theorem hcomp_refl_eval {z : M} {c : Path y z}
    (F : ShortHomotopy (I := I) L p q) (t : unitInterval) :
    (F.hom.hcomp (Path.Homotopy.refl c)).eval t =
      (F.hom.eval t).trans c := by
  ext s
  change
    (F.hom.hcomp (Path.Homotopy.refl c)) (t, s) =
      ((F.hom.eval t).trans c) s
  rw [Path.Homotopy.hcomp_apply]
  by_cases hs : (s : Real) ≤ 1 / 2
  · simp only [hs, ↓reduceDIte, Path.trans_apply]
  · simp only [hs, ↓reduceDIte, Path.trans_apply]
    change (Path.Homotopy.refl c) (t, _) = _
    rw [Path.Homotopy.refl_apply]

noncomputable def appendRight {z : M} {c : Path y z}
    (F : ShortHomotopy (I := I) L p q)
    (hc : IsFlatC1Path (I := I) c) :
    ShortHomotopy (I := I) (L + pathLen (I := I) c)
      (p.trans c) (q.trans c) where
  hom := F.hom.hcomp (Path.Homotopy.refl c)
  flat t := by
    rw [hcomp_refl_eval F t]
    exact (F.flat t).trans hc
  length_le t := by
    rw [hcomp_refl_eval F t, pathLen_trans (F.flat t) hc]
    exact add_le_add (F.length_le t) le_rfl

end ShortHomotopy

end CGT
end Riemannian
end Geometry
end DifferentialGeometry
