import SigmaRealProjectiveComplexification
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.NormedSpace.Connected
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

namespace Sigma
noncomputable section
open scoped LinearAlgebra.Projectivization BigOperators

abbrev RealUnitSphere3 := {v : Fin 3 → ℝ // ∑ i, v i ^ 2 = 1}

private abbrev RealDisk2 := Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1

private instance realDisk2_compact : CompactSpace RealDisk2 := by
  exact isCompact_iff_compactSpace.mp
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)

private def diskRadial (t : Set.Icc (0 : ℝ) 1) (x : RealDisk2) : RealDisk2 :=
  ⟨t.1 • x.1, by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg t.2.1]
    have hx : ‖x.1‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using x.2
    nlinarith [t.2.2, norm_nonneg x.1]⟩

private theorem continuous_diskRadial :
    Continuous (fun p : Set.Icc (0 : ℝ) 1 × RealDisk2 => diskRadial p.1 p.2) := by
  have hc : Continuous (fun p : Set.Icc (0 : ℝ) 1 × RealDisk2 => p.1.1 • p.2.1) :=
    (continuous_subtype_val.comp continuous_fst).smul
      (continuous_subtype_val.comp continuous_snd)
  exact hc.subtype_mk (fun p => by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg p.1.2.1]
    have hx : ‖p.2.1‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using p.2.2
    nlinarith [p.1.2.2, norm_nonneg p.2.1])

private def diskRadialHomotopy (f : RealDisk2 → ℂ)
    (p : Set.Icc (0 : ℝ) 1 × RealDisk2) : ℂ :=
  f (diskRadial p.1 p.2)

private theorem continuous_diskRadialHomotopy (f : RealDisk2 → ℂ)
    (hf : Continuous f) : Continuous (diskRadialHomotopy f) :=
  hf.comp continuous_diskRadial

private abbrev unitInterval := {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1}

private def unitIntervalZero : unitInterval := ⟨0, by simp⟩
private def unitIntervalOne : unitInterval := ⟨1, by simp⟩

private def diskOrigin : RealDisk2 :=
  ⟨0, by simp [Metric.mem_closedBall, dist_eq_norm]⟩

private theorem diskRadial_zero (x : RealDisk2) :
    diskRadial unitIntervalZero x = diskOrigin := by
  apply Subtype.ext
  change (0 : ℝ) • x.1 = 0
  simp [diskRadial, unitIntervalZero, diskOrigin]

private theorem diskRadial_one (x : RealDisk2) :
    diskRadial unitIntervalOne x = x := by
  apply Subtype.ext
  change (1 : ℝ) • x.1 = x.1
  simp [diskRadial, unitIntervalOne]

private def northCoordinates (x : RealDisk2) : Fin 3 → ℝ :=
  ![x.1 0, x.1 1, Real.sqrt (1 - (x.1 0) ^ 2 - (x.1 1) ^ 2)]

private theorem northCoordinates_sum_sq (x : RealDisk2) :
    ∑ i : Fin 3, northCoordinates x i ^ 2 = 1 := by
  have hx : (x.1 0) ^ 2 + (x.1 1) ^ 2 ≤ 1 := by
    have hx' := x.2
    change x.1 ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 at hx'
    rw [EuclideanSpace.closedBall_zero_eq 1 (by norm_num)] at hx'
    simpa [Fin.sum_univ_succ] using hx'
  have hsqrt : 0 ≤ 1 - (x.1 0) ^ 2 - (x.1 1) ^ 2 := by linarith
  have hsum : (∑ i : Fin 3, northCoordinates x i ^ 2) =
      (x.1 0) ^ 2 + (x.1 1) ^ 2 +
        (Real.sqrt (1 - (x.1 0) ^ 2 - (x.1 1) ^ 2)) ^ 2 := by
    simp [northCoordinates, Fin.sum_univ_succ]
    ring
  rw [hsum, Real.sq_sqrt hsqrt]
  ring

private def northHemispherePoint (x : RealDisk2) : RealUnitSphere3 :=
  ⟨northCoordinates x, northCoordinates_sum_sq x⟩

private theorem continuous_northHemispherePoint :
    Continuous northHemispherePoint := by
  have h0 : Continuous (fun x : RealDisk2 => x.1 0) :=
    (continuous_apply 0).comp continuous_subtype_val
  have h1 : Continuous (fun x : RealDisk2 => x.1 1) :=
    (continuous_apply 1).comp continuous_subtype_val
  have h2 : Continuous (fun x : RealDisk2 =>
      Real.sqrt (1 - (x.1 0) ^ 2 - (x.1 1) ^ 2)) :=
    Real.continuous_sqrt.comp ((continuous_const.sub (h0.pow 2)).sub (h1.pow 2))
  have hc : Continuous northCoordinates := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp [northCoordinates] <;> assumption
  exact hc.subtype_mk northCoordinates_sum_sq

private abbrev RealCircle2 :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1

private def equatorDiskPoint (x : RealCircle2) : RealDisk2 :=
  ⟨x.1, by
    have hx : dist x.1 0 = 1 := x.2
    rw [dist_eq_norm, sub_zero] at hx
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    rw [hx]
    ⟩

private def diskAntipodal (x : RealDisk2) : RealDisk2 :=
  ⟨-x.1, by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_neg]
    simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using x.2⟩

private def realCircleAntipodal (x : RealCircle2) : RealCircle2 :=
  ⟨-x.1, by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_neg]
    have hx := x.2
    change dist x.1 (0 : EuclideanSpace ℝ (Fin 2)) = 1 at hx
    rw [dist_eq_norm, sub_zero] at hx
    exact hx⟩

private theorem continuous_realCircleAntipodal :
    Continuous realCircleAntipodal := by
  have hc : Continuous (fun x : RealCircle2 => -x.1) :=
    continuous_neg.comp continuous_subtype_val
  exact hc.subtype_mk (fun x => by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_neg]
    have hx := x.2
    change dist x.1 (0 : EuclideanSpace ℝ (Fin 2)) = 1 at hx
    rw [dist_eq_norm, sub_zero] at hx
    exact hx)

private theorem realCircleAntipodal_involutive (x : RealCircle2) :
    realCircleAntipodal (realCircleAntipodal x) = x := by
  apply Subtype.ext
  simp [realCircleAntipodal]

private theorem continuous_equatorDiskPoint : Continuous equatorDiskPoint := by
  exact continuous_subtype_val.subtype_mk (fun x => (equatorDiskPoint x).2)

private theorem equatorDiskPoint_antipodal (x : RealCircle2) :
    equatorDiskPoint (realCircleAntipodal x) = diskAntipodal (equatorDiskPoint x) := by
  apply Subtype.ext
  rfl

private def realCircleBasepoint : RealCircle2 :=
  ⟨EuclideanSpace.single 0 (1 : ℝ), by
    simp [Metric.mem_sphere, dist_eq_norm, sub_zero, EuclideanSpace.norm_single]⟩

private theorem fin2_coordinate_sum_sq (x : EuclideanSpace ℝ (Fin 2)) :
    (∑ i : Fin 2, x i ^ 2) = ‖x‖ ^ 2 := by
  calc
    (∑ i : Fin 2, x i ^ 2) = ∑ i : Fin 2, ‖x i‖ ^ 2 := by
      simp only [Real.norm_eq_abs, sq_abs]
    _ = (Real.sqrt (∑ i : Fin 2, ‖x i‖ ^ 2)) ^ 2 := by
      rw [Real.sq_sqrt]
      positivity
    _ = ‖x‖ ^ 2 := by rw [EuclideanSpace.norm_eq]

private theorem realCircle2_coordinate_sum (x : RealCircle2) :
    (x.1 0) ^ 2 + (x.1 1) ^ 2 = 1 := by
  have hx : ‖x.1‖ = 1 := by
    have hxmem := x.2
    change dist x.1 (0 : EuclideanSpace ℝ (Fin 2)) = 1 at hxmem
    rw [dist_eq_norm, sub_zero] at hxmem
    exact hxmem
  have hs := fin2_coordinate_sum_sq x.1
  rw [hx] at hs
  simpa [Fin.sum_univ_succ] using hs

private theorem real_euclidean_two_rank :
    1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 2)) := by
  rw [← Module.finrank_eq_rank]
  norm_num

private theorem realCircle2_pathConnected :
    IsPathConnected (Set.univ : Set RealCircle2) := by
  have hs : IsPathConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    isPathConnected_sphere real_euclidean_two_rank 0 (by norm_num)
  letI : PathConnectedSpace RealCircle2 :=
    isPathConnected_iff_pathConnectedSpace.mp hs
  exact pathConnectedSpace_iff_univ.mp inferInstance

private def unitGridTime (N k : ℕ) : unitInterval :=
  ⟨min ((k : ℝ) / N) 1,
    ⟨le_min (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by norm_num),
      min_le_right _ _⟩⟩

private def gridSample {X : Type*} [TopologicalSpace X]
    (H : unitInterval × X → ℂ) (N k : ℕ) (x : X) : ℂ :=
  H (unitGridTime N k, x)

private def gridRatio {X : Type*} [TopologicalSpace X]
    (H : unitInterval × X → ℂ) (N k : ℕ) (x : X) : ℂ :=
  gridSample H N (k + 1) x / gridSample H N k x

private theorem unit_complex_exp_arg {z : ℂ} (hz : ‖z‖ = 1) :
    Complex.exp (Complex.arg z * Complex.I) = z := by
  have habs : Complex.abs z = 1 := by
    rw [← Complex.norm_eq_abs]
    exact hz
  have h := Complex.abs_mul_exp_arg_mul_I z
  rw [habs] at h
  simpa using h

/-- A uniformly fine subdivision lifts a circle-valued null homotopy to a
continuous real angle. The compact-disk application supplies the subdivision
from uniform continuity of the radial contraction. -/
private theorem circle_homotopy_endpoint_has_angle
    {X : Type*} [TopologicalSpace X]
    (H : unitInterval × X → ℂ) (hH : Continuous H)
    (N : ℕ) (hN : 0 < N) (z₀ : ℂ)
    (hstart : ∀ x, H (unitIntervalZero, x) = z₀)
    (hnorm : ∀ t x, ‖H (t, x)‖ = 1)
    (hstep : ∀ k < N, ∀ x,
      ‖gridSample H N (k + 1) x - gridSample H N k x‖ < 1) :
    ∃ θ : X → ℝ, Continuous θ ∧
      ∀ x, Complex.exp ((θ x : ℂ) * Complex.I) = H (unitIntervalOne, x) := by
  have htime0 : unitGridTime N 0 = unitIntervalZero := by
    apply Subtype.ext
    simp [unitGridTime, unitIntervalZero]
  have htimeN : unitGridTime N N = unitIntervalOne := by
    apply Subtype.ext
    have hNc : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    simp [unitGridTime, unitIntervalOne, hNc]
  have hsample (k : ℕ) : Continuous (fun x => gridSample H N k x) := by
    exact hH.comp (continuous_const.prod_mk continuous_id)
  have hsample_norm (k : ℕ) (x : X) : ‖gridSample H N k x‖ = 1 :=
    hnorm (unitGridTime N k) x
  have hsample_ne (k : ℕ) (x : X) : gridSample H N k x ≠ 0 := by
    intro hz
    have hh := hsample_norm k x
    rw [hz, norm_zero] at hh
    norm_num at hh
  have hratio_norm (k : ℕ) (x : X) : ‖gridRatio H N k x‖ = 1 := by
    simp [gridRatio, norm_div, hsample_norm]
  have hratio_ne (k : ℕ) (x : X) : gridRatio H N k x ≠ 0 := by
    intro hz
    have hh := hratio_norm k x
    rw [hz, norm_zero] at hh
    norm_num at hh
  have hratio_near (k : ℕ) (hk : k < N) (x : X) :
      ‖gridRatio H N k x - 1‖ < 1 := by
    have heq : gridRatio H N k x - 1 =
        (gridSample H N (k + 1) x - gridSample H N k x) /
      gridSample H N k x := by
      dsimp [gridRatio]
      field_simp [hsample_ne k x]
    rw [heq, norm_div, hsample_norm k x]
    simpa using hstep k hk x
  have hratio_slit (k : ℕ) (hk : k < N) (x : X) :
      gridRatio H N k x ∈ Complex.slitPlane := by
    have hh := Complex.mem_slitPlane_of_norm_lt_one (hratio_near k hk x)
    have heq : 1 + (gridRatio H N k x - 1) = gridRatio H N k x := by ring
    rw [heq] at hh
    exact hh
  have hratio_cont (k : ℕ) (hk : k < N) :
      Continuous (fun x => gridRatio H N k x) := by
    exact (hsample (k + 1)).div (hsample k) (fun x => hsample_ne k x)
  have hangle_cont (k : ℕ) (hk : k < N) :
      Continuous (fun x => Complex.arg (gridRatio H N k x)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (Complex.continuousAt_arg (hratio_slit k hk x)).comp
      (hratio_cont k hk).continuousAt
  let θ : X → ℝ := fun x => Complex.arg z₀ +
    ∑ k ∈ Finset.range N, Complex.arg (gridRatio H N k x)
  have hθ : Continuous θ := by
    apply continuous_const.add
    apply continuous_finset_sum
    intro k hk
    exact hangle_cont k (Finset.mem_range.mp hk)
  have hprod (x : X) (m : ℕ) :
      (∏ k ∈ Finset.range m, gridRatio H N k x) =
        gridSample H N m x / gridSample H N 0 x := by
    induction m with
    | zero => simp [hsample_ne]
    | succ m ih =>
      rw [Finset.prod_range_succ]
      rw [ih]
      dsimp [gridRatio]
      field_simp [hsample_ne m x, hsample_ne 0 x, hsample_ne (m + 1) x]
      ring
  have hsumexp (x : X) :
      Complex.exp ((∑ k ∈ Finset.range N,
        Complex.arg (gridRatio H N k x) : ℝ) * Complex.I) =
        ∏ k ∈ Finset.range N, gridRatio H N k x := by
    have hcast : ((∑ k ∈ Finset.range N,
        Complex.arg (gridRatio H N k x) : ℝ) : ℂ) * Complex.I =
        ∑ k ∈ Finset.range N,
          (Complex.arg (gridRatio H N k x) : ℂ) * Complex.I := by
      rw [Complex.ofReal_sum, Finset.sum_mul]
    rw [hcast, Complex.exp_sum]
    apply Finset.prod_congr rfl
    intro k hk
    exact unit_complex_exp_arg (hratio_norm k x)
  refine ⟨θ, ⟨hθ, ?_⟩⟩
  intro x
  dsimp [θ]
  rw [Complex.ofReal_add, add_mul, Complex.exp_add]
  rw [unit_complex_exp_arg (by rw [← hstart x]; exact hnorm unitIntervalZero x), hsumexp, hprod]
  have hzero : gridSample H N 0 x = z₀ := by
    simpa [gridSample, htime0] using hstart x
  have hone : gridSample H N N x = H (unitIntervalOne, x) := by
    simp [gridSample, htimeN]
  rw [hzero, hone]
  have hz₀ : z₀ ≠ 0 := by
    intro hz
    have hh := hnorm unitIntervalZero x
    rw [hstart x, hz, norm_zero] at hh
    norm_num at hh
  field_simp [hz₀]

private theorem radial_disk_map_has_angle
    (f : RealDisk2 → ℂ) (hf : Continuous f)
    (hnorm : ∀ x, ‖f x‖ = 1) :
    ∃ θ : RealDisk2 → ℝ, Continuous θ ∧
      ∀ x, Complex.exp ((θ x : ℂ) * Complex.I) = f x := by
  letI : CompactSpace unitInterval :=
    isCompact_iff_compactSpace.mp (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1))
  let H : unitInterval × RealDisk2 → ℂ := diskRadialHomotopy f
  have hH : Continuous H := continuous_diskRadialHomotopy f hf
  have hUC := CompactSpace.uniformContinuous_of_continuous hH
  obtain ⟨δ, hδ, hclose⟩ := (Metric.uniformContinuous_iff.mp hUC) 1 zero_lt_one
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  let N := n + 1
  have hN : 0 < N := Nat.succ_pos n
  have hmesh : 1 / (N : ℝ) < δ := by simpa [N] using hn
  have htime_le (k : ℕ) (hk : k ≤ N) :
      ((k : ℝ) / N) ≤ 1 := by
    have hk' : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk
    exact (div_le_one₀ (by positivity : (0 : ℝ) < N)).2 hk'
  have hstep (k : ℕ) (hk : k < N) (x : RealDisk2) :
      ‖gridSample H N (k + 1) x - gridSample H N k x‖ < 1 := by
    have hk1 : k + 1 ≤ N := Nat.succ_le_of_lt hk
    have ht0 : min ((k : ℝ) / N) 1 = (k : ℝ) / N := min_eq_left (htime_le k (Nat.le_of_lt hk))
    have ht1 : min (((k + 1 : ℕ) : ℝ) / N) 1 = ((k + 1 : ℕ) : ℝ) / N :=
      min_eq_left (htime_le (k + 1) hk1)
    have hdistTime : dist (unitGridTime N k) (unitGridTime N (k + 1)) = 1 / (N : ℝ) := by
      change dist (min ((k : ℝ) / N) 1) (min (((k + 1 : ℕ) : ℝ) / N) 1) = _
      rw [ht0, ht1, dist_eq_norm, Real.norm_eq_abs]
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
      have htimes : (k : ℝ) / N < ((k + 1 : ℕ) : ℝ) / N :=
        (div_lt_div_iff_of_pos_right hNpos).2 (by exact_mod_cast Nat.lt_succ_self k)
      rw [abs_of_nonpos (sub_nonpos.mpr htimes.le)]
      have hNcast : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      field_simp [hNcast]
    have hpair : dist (unitGridTime N k, x) (unitGridTime N (k + 1), x) < δ := by
      rw [Prod.dist_eq, dist_self, max_eq_left (show 0 ≤
        dist (unitGridTime N k) (unitGridTime N (k + 1)) from dist_nonneg), hdistTime]
      exact hmesh
    have hout := hclose hpair
    simpa [gridSample, diskRadialHomotopy, dist_eq_norm, norm_sub_rev] using hout
  have hstart (x : RealDisk2) : H (unitIntervalZero, x) = f diskOrigin := by
    simp [H, diskRadialHomotopy, diskRadial_zero]
  have hnormH (t : unitInterval) (x : RealDisk2) : ‖H (t, x)‖ = 1 := by
    exact hnorm (diskRadial t x)
  obtain ⟨θ, hθ, hθexp⟩ :=
    circle_homotopy_endpoint_has_angle H hH N hN (f diskOrigin) hstart hnormH hstep
  refine ⟨θ, hθ, ?_⟩
  intro x
  rw [hθexp x]
  simp [H, diskRadialHomotopy, diskRadial_one]

private theorem real_euclidean_three_rank :
    1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 3)) := by
  rw [← Module.finrank_eq_rank]
  norm_num

private theorem real_euclidean_sphere_coordinates
    (x : EuclideanSpace ℝ (Fin 3)) (hx : ‖x‖ = 1) :
    ∑ i, (EuclideanSpace.equiv (Fin 3) ℝ x) i ^ 2 = 1 := by
  rw [EuclideanSpace.norm_eq] at hx
  have hsum : 0 ≤ ∑ i, ‖x i‖ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hh := congrArg (fun z : ℝ => z ^ 2) hx
  change (Real.sqrt (∑ i, ‖x i‖ ^ 2)) ^ 2 = 1 ^ 2 at hh
  rw [Real.sq_sqrt hsum] at hh
  norm_num at hh
  simpa only [EuclideanSpace.equiv, PiLp.continuousLinearEquiv,
    Real.norm_eq_abs, sq_abs] using hh

/-- The normalized coordinate sphere used for the tautological pullback is
homeomorphic to the ordinary Euclidean unit sphere. -/
def realUnitSphere3Homeomorph :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₜ RealUnitSphere3 where
  toFun x := ⟨EuclideanSpace.equiv (Fin 3) ℝ x.1, by
    have hn : ‖x.1‖ = 1 := by
      simp [Metric.mem_sphere, dist_eq_norm]
    exact real_euclidean_sphere_coordinates x.1 hn⟩
  invFun v := ⟨(EuclideanSpace.equiv (Fin 3) ℝ).symm v.1, by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, EuclideanSpace.norm_eq]
    have hv : ∑ i, ‖((EuclideanSpace.equiv (Fin 3) ℝ).symm v.1) i‖ ^ 2 = 1 := by
      simpa only [EuclideanSpace.equiv, PiLp.continuousLinearEquiv,
        Real.norm_eq_abs, sq_abs] using v.2
    rw [hv]
    simp⟩
  left_inv x := by
    apply Subtype.ext
    exact (EuclideanSpace.equiv (Fin 3) ℝ).apply_symm_apply x.1
  right_inv v := by
    apply Subtype.ext
    exact (EuclideanSpace.equiv (Fin 3) ℝ).apply_symm_apply v.1
  continuous_toFun := by
    exact ((EuclideanSpace.equiv (Fin 3) ℝ).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    exact ((EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp continuous_subtype_val).subtype_mk _

theorem realUnitSphere3_pathConnected : IsPathConnected (Set.univ : Set RealUnitSphere3) := by
  have hs : IsPathConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    isPathConnected_sphere real_euclidean_three_rank 0 (by norm_num)
  letI : PathConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp hs
  exact pathConnectedSpace_iff_univ.mp
    (realUnitSphere3Homeomorph.surjective.pathConnectedSpace
      realUnitSphere3Homeomorph.continuous_toFun)

private theorem real_unit_sphere_nonzero (v : RealUnitSphere3) : v.1 ≠ 0 := by
  intro hv
  have h := v.2
  simp [hv] at h

def realUnitSphereProjective (v : RealUnitSphere3) : RealProjectivePlane :=
  Projectivization.mk ℝ v.1 (real_unit_sphere_nonzero v)

theorem real_unit_sphere_projective_continuous :
    Continuous realUnitSphereProjective := by
  change Continuous (fun v : RealUnitSphere3 =>
    Projectivization.mk' ℝ ⟨v.1, real_unit_sphere_nonzero v⟩)
  exact continuous_coinduced_rng.comp (by fun_prop)

theorem real_unit_sphere_projective_antipodal (v : RealUnitSphere3) :
    realUnitSphereProjective ⟨-v.1, by simp [v.2]⟩ = realUnitSphereProjective v := by
  apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
  refine ⟨-1, ?_⟩
  ext i
  simp

/-- A nowhere-zero continuous section of the actual complexified tautological
line, written in its incidence-space realization. -/
structure NonvanishingRealProjectiveComplexSection where
  value : RealProjectivePlane → Fin 3 → ℂ
  continuous_value : Continuous value
  fiber : ∀ p, value p ∈ (realProjectiveComplexification p).submodule
  nonzero : ∀ p, value p ≠ 0

/-- A genuine global vector-bundle trivialization of the constructed line:
the total-space homeomorphism lies over the identity and its fiber maps are
complex-linear equivalences. -/
structure RealProjectiveComplexBundleTrivialization where
  totalHomeomorph : realProjectiveComplexCore.TotalSpace ≃ₜ
    (RealProjectivePlane × (Fin 1 → ℂ))
  fiberEquiv : ∀ p, realProjectiveComplexCore.Fiber p ≃ₗ[ℂ] (Fin 1 → ℂ)
  total_apply : ∀ (p : RealProjectivePlane) (z : realProjectiveComplexCore.Fiber p),
    totalHomeomorph ⟨p, z⟩ = (p, fiberEquiv p z)

private def trivializationUnitVector : Fin 1 → ℂ := fun _ => 1

private theorem trivializationUnitVector_ne_zero : trivializationUnitVector ≠ 0 := by
  intro h
  have hh := congrFun h 0
  norm_num [trivializationUnitVector] at hh

private def sectionFromTrivializationPoint
    (T : RealProjectiveComplexBundleTrivialization) (p : RealProjectivePlane) :
    realProjectiveComplexCore.TotalSpace :=
  ⟨p, (T.fiberEquiv p).symm trivializationUnitVector⟩

private def incidenceSectionFromTrivialization
    (T : RealProjectiveComplexBundleTrivialization) (p : RealProjectivePlane) :
    RealProjectiveComplexIncidence :=
  realProjectiveComplexIncidenceHomeomorph (sectionFromTrivializationPoint T p)

private theorem continuous_sectionFromTrivializationPoint
    (T : RealProjectiveComplexBundleTrivialization) :
    Continuous (sectionFromTrivializationPoint T) := by
  have heq : sectionFromTrivializationPoint T = fun p =>
      T.totalHomeomorph.symm (p, trivializationUnitVector) := by
    funext p
    apply T.totalHomeomorph.injective
    change T.totalHomeomorph ⟨p, (T.fiberEquiv p).symm trivializationUnitVector⟩ = _
    calc
      _ = (p, trivializationUnitVector) := by
        rw [T.total_apply]
        simp
      _ = T.totalHomeomorph (T.totalHomeomorph.symm (p, trivializationUnitVector)) :=
        (T.totalHomeomorph.apply_symm_apply _).symm
  rw [heq]
  exact T.totalHomeomorph.continuous_invFun.comp
    (continuous_id.prod_mk continuous_const)

private theorem continuous_incidenceSectionFromTrivialization
    (T : RealProjectiveComplexBundleTrivialization) :
    Continuous (incidenceSectionFromTrivialization T) :=
  realProjectiveComplexIncidenceHomeomorph.continuous_toFun.comp
    (continuous_sectionFromTrivializationPoint T)

/-- A trivialization would give an actual continuous nowhere-zero section of
the incidence realization of the complexified tautological line. -/
private def sectionDataOfBundleTrivialization
    (T : RealProjectiveComplexBundleTrivialization) :
    NonvanishingRealProjectiveComplexSection where
  value p := (incidenceSectionFromTrivialization T p).val.2
  continuous_value :=
    continuous_snd.comp
      (continuous_subtype_val.comp (continuous_incidenceSectionFromTrivialization T))
  fiber p := (incidenceSectionFromTrivialization T p).property
  nonzero p := by
    intro hz
    let z := (T.fiberEquiv p).symm trivializationUnitVector
    have hmap : realProjectiveComplexFiberMap p z = 0 := by
      apply Subtype.ext
      exact hz
    have hz0 : z = 0 := (real_projective_complex_fiber_map_bijective p).1 (by simpa using hmap)
    have hunit : trivializationUnitVector = 0 := by
      have hh := congrArg (T.fiberEquiv p) hz0
      simpa [z] using hh
    exact trivializationUnitVector_ne_zero hunit

def realProjectiveSectionCoefficient (s : NonvanishingRealProjectiveComplexSection)
    (v : RealUnitSphere3) : ℂ :=
  ∑ i, (v.1 i : ℂ) * s.value (realUnitSphereProjective v) i

private theorem real_projective_section_coefficient_eq_scalar
    (s : NonvanishingRealProjectiveComplexSection) (v : RealUnitSphere3)
    {c : ℂ}
    (hc : s.value (realUnitSphereProjective v) =
      c • realCoordinateComplexification v.1) :
    realProjectiveSectionCoefficient s v = c := by
  rw [realProjectiveSectionCoefficient, hc]
  simp only [realCoordinateComplexification, Pi.smul_apply, smul_eq_mul,
    Complex.ofReal_mul, Finset.mul_sum]
  calc
    ∑ i, (v.1 i : ℂ) * (c * (v.1 i : ℂ))
        = c * ∑ i, (v.1 i : ℂ) * (v.1 i : ℂ) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
    _ = c := by
      have hsum : (∑ i, (v.1 i : ℂ) * (v.1 i : ℂ)) = 1 := by
        have h : (∑ i, v.1 i ^ 2 : ℝ) = 1 := v.2
        norm_cast at h ⊢
        simpa [pow_two] using h
      rw [hsum, mul_one]

theorem real_projective_section_coefficient_ne_zero
    (s : NonvanishingRealProjectiveComplexSection) (v : RealUnitSphere3) :
    realProjectiveSectionCoefficient s v ≠ 0 := by
  have hm : s.value (realUnitSphereProjective v) ∈
      ℂ ∙ realCoordinateComplexification v.1 := by
    have hp : realProjectiveComplexification (realUnitSphereProjective v) =
        Projectivization.mk ℂ (realCoordinateComplexification v.1) (by
          intro hz
          apply real_unit_sphere_nonzero v
          exact real_coordinate_complexification_injective hz) :=
      real_projective_complexification_mk v.1 (real_unit_sphere_nonzero v)
    have hf := s.fiber (realUnitSphereProjective v)
    rw [hp, Projectivization.submodule_mk] at hf
    exact hf
  rw [Submodule.mem_span_singleton] at hm
  obtain ⟨c, hc⟩ := hm
  have hc' := hc.symm
  have hcoeff := real_projective_section_coefficient_eq_scalar s v hc'
  intro hz
  have hc0 : c = 0 := by rw [← hcoeff]; exact hz
  exact s.nonzero _ (by rw [hc', hc0]; simp)

private def realUnitSphereAntipodal (v : RealUnitSphere3) : RealUnitSphere3 :=
  ⟨-v.1, by simp [v.2]⟩

private theorem north_equator_antipodal (x : RealCircle2) :
    northHemispherePoint (diskAntipodal (equatorDiskPoint x)) =
      realUnitSphereAntipodal (northHemispherePoint (equatorDiskPoint x)) := by
  have hsum := realCircle2_coordinate_sum x
  have hz : 1 - (x.1 0) ^ 2 - (x.1 1) ^ 2 = 0 := by linarith
  apply Subtype.ext
  funext i
  fin_cases i <;>
    simp [northHemispherePoint, northCoordinates, diskAntipodal,
      equatorDiskPoint, realUnitSphereAntipodal, hz]

theorem real_projective_section_coefficient_odd
    (s : NonvanishingRealProjectiveComplexSection) (v : RealUnitSphere3) :
    realProjectiveSectionCoefficient s (realUnitSphereAntipodal v) =
      -realProjectiveSectionCoefficient s v := by
  unfold realUnitSphereAntipodal
  rw [realProjectiveSectionCoefficient, realProjectiveSectionCoefficient,
    real_unit_sphere_projective_antipodal]
  simp only [realUnitSphereAntipodal, Subtype.coe_mk, Pi.neg_apply, Complex.ofReal_neg,
    neg_mul, Finset.sum_neg_distrib]

def realProjectiveSectionPhase (s : NonvanishingRealProjectiveComplexSection)
    (v : RealUnitSphere3) : ℂ :=
  realProjectiveSectionCoefficient s v /
    (‖realProjectiveSectionCoefficient s v‖ : ℂ)

theorem real_projective_section_phase_norm (s : NonvanishingRealProjectiveComplexSection)
    (v : RealUnitSphere3) : ‖realProjectiveSectionPhase s v‖ = 1 := by
  rw [realProjectiveSectionPhase, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact div_self (ne_of_gt (norm_pos_iff.mpr
    (real_projective_section_coefficient_ne_zero s v)))

theorem real_projective_section_phase_odd (s : NonvanishingRealProjectiveComplexSection)
    (v : RealUnitSphere3) :
    realProjectiveSectionPhase s (realUnitSphereAntipodal v) =
      -realProjectiveSectionPhase s v := by
  rw [realProjectiveSectionPhase, real_projective_section_coefficient_odd]
  simp only [norm_neg, neg_div]
  rfl

theorem real_projective_section_phase_continuous
    (s : NonvanishingRealProjectiveComplexSection) :
    Continuous (realProjectiveSectionPhase s) := by
  have hc : Continuous (realProjectiveSectionCoefficient s) := by
    unfold realProjectiveSectionCoefficient
    apply continuous_finset_sum
    intro i hi
    exact (Complex.continuous_ofReal.comp
      ((continuous_apply i).comp continuous_subtype_val)).mul
      ((continuous_apply i).comp (s.continuous_value.comp real_unit_sphere_projective_continuous))
  unfold realProjectiveSectionPhase
  apply Continuous.div hc (Complex.continuous_ofReal.comp (continuous_norm.comp hc))
  intro v
  change (‖realProjectiveSectionCoefficient s v‖ : ℂ) ≠ 0
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (norm_pos_iff.mpr
    (real_projective_section_coefficient_ne_zero s v)))

private theorem complex_exp_real_pi_I :
    Complex.exp ((Real.pi : ℂ) * Complex.I) = -1 := by
  rw [Complex.exp_mul_I]
  norm_num

/-- The final angle-lift contradiction in the paper's odd-map argument. -/
theorem odd_unit_phase_has_no_continuous_angle
    (g : RealUnitSphere3 → ℂ)
    (hodd : ∀ v, g (realUnitSphereAntipodal v) = -g v)
    (θ : RealUnitSphere3 → ℝ) (hθ : Continuous θ)
    (hθexp : ∀ v, Complex.exp ((θ v : ℂ) * Complex.I) = g v) : False := by
  have ha : Continuous realUnitSphereAntipodal := by
    unfold realUnitSphereAntipodal
    apply (continuous_neg.comp continuous_subtype_val).subtype_mk
  let δ : RealUnitSphere3 → ℝ := fun v => θ (realUnitSphereAntipodal v) - θ v
  have hδ : Continuous δ := by
    dsimp [δ]
    exact hθ.comp ha |>.sub hθ
  have hδexp (v : RealUnitSphere3) : Complex.exp ((δ v : ℂ) * Complex.I) = -1 := by
    change Complex.exp (((θ (realUnitSphereAntipodal v) - θ v : ℝ) : ℂ) * Complex.I) = -1
    rw [Complex.ofReal_sub, sub_mul, Complex.exp_sub, hθexp, hθexp, hodd]
    have hz : g v ≠ 0 := by
      rw [← hθexp v]
      exact Complex.exp_ne_zero _
    simp [hz]
  have conn := realUnitSphere3_pathConnected.isConnected.isPreconnected
  have hincrease (a b : RealUnitSphere3) (hab : δ a < δ b) : False := by
    obtain ⟨k, hk⟩ := (Complex.exp_eq_exp_iff_exists_int).mp
      ((hδexp b).trans (hδexp a).symm)
    have hkc : (δ b : ℂ) = (δ a : ℂ) + (k : ℂ) * (2 * Real.pi) := by
      apply (mul_left_inj' Complex.I_ne_zero).mp
      calc
        (δ b : ℂ) * Complex.I = (δ a : ℂ) * Complex.I + (k : ℂ) * (2 * Real.pi * Complex.I) := hk
        _ = ((δ a : ℂ) + (k : ℂ) * (2 * Real.pi)) * Complex.I := by ring
    have hkR : δ b = δ a + (k : ℝ) * (2 * Real.pi) := by exact_mod_cast hkc
    have hkpos : (1 : ℝ) ≤ (k : ℝ) := by
      have hkpos0 : (0 : ℝ) < (k : ℝ) := by nlinarith [hkR, hab, Real.pi_pos]
      have hki : 0 < k := by exact_mod_cast hkpos0
      have hkge : 1 ≤ k := by omega
      exact_mod_cast hkge
    let c : ℝ := δ a + Real.pi
    have hleft : δ a ≤ c := by dsimp [c]; linarith [Real.pi_pos]
    have hright : c ≤ δ b := by
      rw [hkR]
      dsimp [c]
      nlinarith [Real.pi_pos, hkpos]
    have hmid := conn.intermediate_value (Set.mem_univ a) (Set.mem_univ b)
      hδ.continuousOn (show c ∈ Set.Icc (δ a) (δ b) from ⟨hleft, hright⟩)
    obtain ⟨u, hu, huc⟩ := hmid
    have huc' : δ u = δ a + Real.pi := by simpa [c] using huc
    have hplus : Complex.exp (((δ a + Real.pi : ℝ) : ℂ) * Complex.I) = 1 := by
      calc
        _ = Complex.exp ((δ a : ℂ) * Complex.I) *
            Complex.exp ((Real.pi : ℂ) * Complex.I) := by
              rw [Complex.ofReal_add, add_mul, Complex.exp_add]
        _ = 1 := by rw [hδexp a, complex_exp_real_pi_I]; norm_num
    have hbad := hδexp u
    rw [huc'] at hbad
    rw [hplus] at hbad
    norm_num at hbad
  have hδconst : ∀ a b : RealUnitSphere3, δ a = δ b := by
    intro a b
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hincrease a b hlt
    · exact (hincrease b a hgt).elim
  have hantipodal (v : RealUnitSphere3) :
      realUnitSphereAntipodal (realUnitSphereAntipodal v) = v := by
    apply Subtype.ext
    simp [realUnitSphereAntipodal]
  have hdneg (v : RealUnitSphere3) : δ (realUnitSphereAntipodal v) = -δ v := by
    dsimp [δ]
    rw [hantipodal]
    ring
  have hzero (v : RealUnitSphere3) : δ v = 0 := by
    have hh := hδconst v (realUnitSphereAntipodal v)
    rw [hdneg] at hh
    linarith
  let v₀ : RealUnitSphere3 := ⟨Pi.single 0 (1 : ℝ), by
    simp only [Pi.single_apply]
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
    norm_num
    all_goals decide⟩
  have hz₀ := hzero v₀
  have he₀ := hδexp v₀
  rw [hz₀] at he₀
  have hcontr : (1 : ℂ) = -1 := by simpa using he₀
  exact (by norm_num : (1 : ℂ) ≠ -1) hcontr

/-- A section of the actual complexified tautological line would give the
paper's forbidden odd circle map; once its global angle lift is constructed,
connectedness supplies the contradiction. -/
theorem real_projective_complex_section_forces_impossible_angle
    (s : NonvanishingRealProjectiveComplexSection)
    (θ : RealUnitSphere3 → ℝ) (hθ : Continuous θ)
    (hθexp : ∀ v, Complex.exp ((θ v : ℂ) * Complex.I) = realProjectiveSectionPhase s v) :
    False :=
  odd_unit_phase_has_no_continuous_angle (realProjectiveSectionPhase s)
    (real_projective_section_phase_odd s) θ hθ hθexp

private theorem odd_angle_lift_impossible_of_preconnected
    {X : Type*} [TopologicalSpace X]
    (hconn : IsPreconnected (Set.univ : Set X)) (x₀ : X)
    (A : X → X) (hA : Continuous A) (hA2 : ∀ x, A (A x) = x)
    (g : X → ℂ) (hodd : ∀ x, g (A x) = -g x)
    (θ : X → ℝ) (hθ : Continuous θ)
    (hθexp : ∀ x, Complex.exp ((θ x : ℂ) * Complex.I) = g x) : False := by
  let δ : X → ℝ := fun x => θ (A x) - θ x
  have hδ : Continuous δ := by
    dsimp [δ]
    exact (hθ.comp hA).sub hθ
  have hδexp (x : X) : Complex.exp ((δ x : ℂ) * Complex.I) = -1 := by
    change Complex.exp (((θ (A x) - θ x : ℝ) : ℂ) * Complex.I) = -1
    rw [Complex.ofReal_sub, sub_mul, Complex.exp_sub, hθexp, hθexp, hodd]
    have hz : g x ≠ 0 := by
      rw [← hθexp x]
      exact Complex.exp_ne_zero _
    simp [hz]
  have hincrease (a b : X) (hab : δ a < δ b) : False := by
    obtain ⟨k, hk⟩ := (Complex.exp_eq_exp_iff_exists_int).mp
      ((hδexp b).trans (hδexp a).symm)
    have hkc : (δ b : ℂ) = (δ a : ℂ) + (k : ℂ) * (2 * Real.pi) := by
      apply (mul_left_inj' Complex.I_ne_zero).mp
      calc
        (δ b : ℂ) * Complex.I = (δ a : ℂ) * Complex.I +
            (k : ℂ) * (2 * Real.pi * Complex.I) := hk
        _ = ((δ a : ℂ) + (k : ℂ) * (2 * Real.pi)) * Complex.I := by ring
    have hkR : δ b = δ a + (k : ℝ) * (2 * Real.pi) := by exact_mod_cast hkc
    have hkpos : (1 : ℝ) ≤ (k : ℝ) := by
      have hkpos0 : (0 : ℝ) < (k : ℝ) := by nlinarith [hkR, hab, Real.pi_pos]
      have hki : 0 < k := by exact_mod_cast hkpos0
      have hkge : 1 ≤ k := by omega
      exact_mod_cast hkge
    let c : ℝ := δ a + Real.pi
    have hleft : δ a ≤ c := by dsimp [c]; linarith [Real.pi_pos]
    have hright : c ≤ δ b := by
      rw [hkR]
      dsimp [c]
      nlinarith [Real.pi_pos, hkpos]
    have hmid := hconn.intermediate_value (Set.mem_univ a) (Set.mem_univ b)
      hδ.continuousOn (show c ∈ Set.Icc (δ a) (δ b) from ⟨hleft, hright⟩)
    obtain ⟨u, hu, huc⟩ := hmid
    have huc' : δ u = δ a + Real.pi := by simpa [c] using huc
    have hplus : Complex.exp (((δ a + Real.pi : ℝ) : ℂ) * Complex.I) = 1 := by
      calc
        _ = Complex.exp ((δ a : ℂ) * Complex.I) *
            Complex.exp ((Real.pi : ℂ) * Complex.I) := by
              rw [Complex.ofReal_add, add_mul, Complex.exp_add]
        _ = 1 := by rw [hδexp a, complex_exp_real_pi_I]; norm_num
    have hbad := hδexp u
    rw [huc'] at hbad
    rw [hplus] at hbad
    norm_num at hbad
  have hδconst : ∀ a b : X, δ a = δ b := by
    intro a b
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hincrease a b hlt
    · exact (hincrease b a hgt).elim
  have hdneg (x : X) : δ (A x) = -δ x := by
    dsimp [δ]
    rw [hA2 x]
    ring
  have hz : δ x₀ = 0 := by
    have hh := hδconst x₀ (A x₀)
    rw [hdneg] at hh
    linarith
  have hbad := hδexp x₀
  rw [hz] at hbad
  have hfalse : (1 : ℂ) = -1 := by simpa using hbad
  exact (by norm_num : (1 : ℂ) ≠ -1) hfalse

/-- The paper's no-section obstruction on the actual tautological complex line.
The angle is constructed on the closed northern hemisphere from the radial
null homotopy; its restriction to the equator contradicts oddness. -/
theorem real_projective_complexification_has_no_nonvanishing_section
    (s : NonvanishingRealProjectiveComplexSection) : False := by
  let f : RealDisk2 → ℂ := fun x =>
    realProjectiveSectionPhase s (northHemispherePoint x)
  have hf : Continuous f :=
    (real_projective_section_phase_continuous s).comp continuous_northHemispherePoint
  have hfnorm (x : RealDisk2) : ‖f x‖ = 1 :=
    real_projective_section_phase_norm s (northHemispherePoint x)
  obtain ⟨θ, hθ, hθexp⟩ := radial_disk_map_has_angle f hf hfnorm
  let g : RealCircle2 → ℂ := fun x => f (equatorDiskPoint x)
  have hg : Continuous g := hf.comp continuous_equatorDiskPoint
  have hodd (x : RealCircle2) :
      g (realCircleAntipodal x) = -g x := by
    change realProjectiveSectionPhase s
        (northHemispherePoint (equatorDiskPoint (realCircleAntipodal x))) = _
    rw [equatorDiskPoint_antipodal, north_equator_antipodal]
    exact real_projective_section_phase_odd s
      (northHemispherePoint (equatorDiskPoint x))
  let θe : RealCircle2 → ℝ := fun x => θ (equatorDiskPoint x)
  have hθe : Continuous θe := hθ.comp continuous_equatorDiskPoint
  have hθeexp (x : RealCircle2) :
      Complex.exp ((θe x : ℂ) * Complex.I) = g x := by
    exact hθexp (equatorDiskPoint x)
  have ha : Continuous realCircleAntipodal := continuous_realCircleAntipodal
  have ha2 := realCircleAntipodal_involutive
  have hconn := realCircle2_pathConnected.isConnected.isPreconnected
  exact odd_angle_lift_impossible_of_preconnected hconn realCircleBasepoint
    realCircleAntipodal ha ha2 g hodd θe hθe hθeexp

theorem real_projective_complex_bundle_not_trivial :
    ¬ Nonempty RealProjectiveComplexBundleTrivialization := by
  rintro ⟨T⟩
  exact real_projective_complexification_has_no_nonvanishing_section
    (sectionDataOfBundleTrivialization T)

end
end Sigma
