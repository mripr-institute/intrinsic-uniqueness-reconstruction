import SigmaPresentations
import Mathlib.Data.Nat.GCD.Basic

namespace Sigma
noncomputable section

def cwLeft (x : ℚ) : ℚ := x / (1 + x)
def cwRight (x : ℚ) : ℚ := 1 + x

theorem cwLeft_positive {x : ℚ} (hx : 0 < x) : 0 < cwLeft x := by
  unfold cwLeft
  positivity

theorem cwLeft_lt_one {x : ℚ} (hx : 0 < x) : cwLeft x < 1 := by
  unfold cwLeft
  apply (div_lt_one (by positivity)).mpr
  linarith

theorem cwRight_gt_one {x : ℚ} (hx : 0 < x) : 1 < cwRight x := by
  unfold cwRight
  linarith

theorem cwLeft_injectiveOn : Set.InjOn cwLeft (Set.Ioi 0) := by
  intro x hx y hy h
  change 0 < x at hx
  change 0 < y at hy
  have hx0 : 1 + x ≠ 0 := ne_of_gt (by linarith)
  have hy0 : 1 + y ≠ 0 := ne_of_gt (by linarith)
  unfold cwLeft at h
  field_simp at h
  nlinarith

/-- The head is the outermost letter, i.e. reverse chronological path order. -/
def cwValue : List Bool → ℚ
  | [] => 1
  | false :: w => cwLeft (cwValue w)
  | true :: w => cwRight (cwValue w)

theorem cwValue_positive (w : List Bool) : 0 < cwValue w := by
  induction w with
  | nil => norm_num [cwValue]
  | cons b w ih =>
    cases b
    · exact cwLeft_positive ih
    · exact lt_trans (by norm_num) (cwRight_gt_one ih)

theorem cwValue_injective : Function.Injective cwValue := by
  intro u
  induction u with
  | nil =>
    intro v h
    cases v with
    | nil => rfl
    | cons b v =>
      cases b
      · have hv := cwLeft_lt_one (cwValue_positive v)
        change 1 = cwLeft (cwValue v) at h
        linarith
      · have hv := cwRight_gt_one (cwValue_positive v)
        change 1 = cwRight (cwValue v) at h
        linarith
  | cons b u ih =>
    intro v h
    cases v with
    | nil =>
      cases b
      · have hu := cwLeft_lt_one (cwValue_positive u)
        change cwLeft (cwValue u) = 1 at h
        linarith
      · have hu := cwRight_gt_one (cwValue_positive u)
        change cwRight (cwValue u) = 1 at h
        linarith
    | cons c v =>
      cases b <;> cases c
      · congr 1
        apply ih
        exact cwLeft_injectiveOn (cwValue_positive u) (cwValue_positive v) h
      · have hu := cwLeft_lt_one (cwValue_positive u)
        have hv := cwRight_gt_one (cwValue_positive v)
        change cwLeft (cwValue u) = cwRight (cwValue v) at h
        linarith
      · have hu := cwRight_gt_one (cwValue_positive u)
        have hv := cwLeft_lt_one (cwValue_positive v)
        change cwRight (cwValue u) = cwLeft (cwValue v) at h
        linarith
      · congr 1
        apply ih
        change 1 + cwValue u = 1 + cwValue v at h
        linarith

theorem cw_parent_below (a b : ℕ) (ha : 0 < a) (hab : a < b) :
    cwLeft ((a : ℚ) / (b - a : ℕ)) = (a : ℚ) / b := by
  have hb : (b : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_trans ha hab))
  have hba : ((b - a : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.sub_pos_of_lt hab))
  rw [Nat.cast_sub (Nat.le_of_lt hab)]
  unfold cwLeft
  have habQ : (a : ℚ) < b := by exact_mod_cast hab
  have hd : (b : ℚ) - a ≠ 0 := ne_of_gt (sub_pos.mpr habQ)
  field_simp [hd, hb]

theorem cw_parent_above (a b : ℕ) (hb : 0 < b) (hba : b < a) :
    cwRight (((a - b : ℕ) : ℚ) / b) = (a : ℚ) / b := by
  have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  rw [Nat.cast_sub (Nat.le_of_lt hba)]
  unfold cwRight
  field_simp

theorem cw_reduced_fraction_exists (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hab : Nat.Coprime a b) : ∃ w : List Bool, cwValue w = (a : ℚ) / b := by
  generalize he : a + b = n
  induction n using Nat.strong_induction_on generalizing a b with
  | h n ih =>
    rcases lt_trichotomy a b with hlt | heq | hgt
    · have hsub : 0 < b - a := Nat.sub_pos_of_lt hlt
      have hcop : Nat.Coprime a (b - a) :=
        (Nat.coprime_sub_self_right (Nat.le_of_lt hlt)).mpr hab
      obtain ⟨w, hw⟩ := ih (a + (b - a)) (by omega) a (b - a) ha hsub hcop rfl
      refine ⟨false :: w, ?_⟩
      change cwLeft (cwValue w) = _
      rw [hw, cw_parent_below a b ha hlt]
    · subst b
      have h1 : a = 1 := by simpa [Nat.Coprime] using hab
      subst a
      exact ⟨[], by norm_num [cwValue]⟩
    · have hsub : 0 < a - b := Nat.sub_pos_of_lt hgt
      have hcop : Nat.Coprime (a - b) b :=
        (Nat.coprime_sub_self_left (Nat.le_of_lt hgt)).mpr hab
      obtain ⟨w, hw⟩ := ih (a - b + b) (by omega) (a - b) b hsub hb hcop rfl
      refine ⟨true :: w, ?_⟩
      change cwRight (cwValue w) = _
      rw [hw, cw_parent_above a b hb hgt]

theorem cw_positive_rational_exists (q : ℚ) (hq : 0 < q) :
    ∃ w : List Bool, cwValue w = q := by
  have hn : 0 < q.num := Rat.num_pos.mpr hq
  have hna : 0 < q.num.natAbs := Int.natAbs_pos.mpr (ne_of_gt hn)
  obtain ⟨w, hw⟩ := cw_reduced_fraction_exists q.num.natAbs q.den hna q.pos q.reduced
  refine ⟨w, ?_⟩
  have he : (q.num.natAbs : ℤ) = q.num := Int.natAbs_of_nonneg (le_of_lt hn)
  have heq : (q.num.natAbs : ℚ) = (q.num : ℚ) := by
    calc
      _ = ((q.num.natAbs : ℤ) : ℚ) := (Int.cast_natCast q.num.natAbs).symm
      _ = (q.num : ℚ) := congrArg (fun z : ℤ => (z : ℚ)) he
  rw [heq, q.num_div_den] at hw
  exact hw

theorem cw_positive_rational_exists_unique (q : ℚ) (hq : 0 < q) :
    ∃! w : List Bool, cwValue w = q := by
  obtain ⟨w, hw⟩ := cw_positive_rational_exists q hq
  exact ⟨w, hw, fun v hv => cwValue_injective (hv.trans hw.symm)⟩

def fareyLeft (x : ℝ) : ℝ := x / (1 + x)
def fareyRight (x : ℝ) : ℝ := 1 / (1 + x)

theorem farey_left_inverse (x : ℝ) (hx : 0 ≤ x) :
    fareyLeft x / (1 - fareyLeft x) = x := by
  have h : 1 + x ≠ 0 := ne_of_gt (by linarith)
  unfold fareyLeft
  field_simp

theorem farey_right_inverse (x : ℝ) (hx : 0 ≤ x) :
    (1 - fareyRight x) / fareyRight x = x := by
  have h : 1 + x ≠ 0 := ne_of_gt (by linarith)
  unfold fareyRight
  field_simp

theorem farey_left_range (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ fareyLeft x ∧ fareyLeft x ≤ 1 / 2 := by
  unfold fareyLeft
  have h : 0 < 1 + x := by linarith
  constructor
  · positivity
  · apply (div_le_iff₀ h).mpr
    linarith

theorem farey_right_range (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    1 / 2 ≤ fareyRight x ∧ fareyRight x ≤ 1 := by
  unfold fareyRight
  have h : 0 < 1 + x := by linarith
  constructor
  · apply (le_div_iff₀ h).mpr
    linarith
  · apply (div_le_one h).mpr
    linarith

def placedCode (mu gamma c x : ℝ) : ℝ := Real.log (1 + gamma * x) - mu * x + c

theorem placed_collision_iff (mu gamma c n m : ℝ)
    (hn : 0 < 1 + gamma * n) (hm : 0 < 1 + gamma * m) (hne : n ≠ m) :
    placedCode mu gamma c n = placedCode mu gamma c m ↔
      mu = Real.log ((1 + gamma * n) / (1 + gamma * m)) / (n - m) := by
  rw [Real.log_div (ne_of_gt hn) (ne_of_gt hm)]
  rw [eq_div_iff (sub_ne_zero.mpr hne)]
  unfold placedCode
  constructor <;> intro h <;> nlinarith

def collisionScaleDifference (gamma k x : ℝ) : ℝ :=
  Real.log (1 + k * gamma * x) - k * Real.log (1 + gamma * x)

theorem collisionScaleDifference_deriv (gamma k x : ℝ)
    (hg : 0 < gamma) (hk : 1 < k) (hx : 0 < x) :
    HasDerivAt (collisionScaleDifference gamma k)
      (k * gamma / (1 + k * gamma * x) - k * (gamma / (1 + gamma * x))) x := by
  have h1 : 1 + k * gamma * x ≠ 0 := ne_of_gt (by positivity)
  have h2 : 1 + gamma * x ≠ 0 := ne_of_gt (by positivity)
  convert (((Real.hasDerivAt_log h1).comp x
    (((hasDerivAt_id x).const_mul (k * gamma)).const_add 1)).sub
      (((Real.hasDerivAt_log h2).comp x
        (((hasDerivAt_id x).const_mul gamma).const_add 1)).const_mul k)) using 1
  ring

theorem collisionScaleDifference_strictAnti (gamma k : ℝ)
    (hg : 0 < gamma) (hk : 1 < k) :
    StrictAntiOn (collisionScaleDifference gamma k) (Set.Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · intro x hx
    exact (collisionScaleDifference_deriv gamma k x hg hk hx).continuousAt.continuousWithinAt
  · intro x hx
    have hx0 : 0 < x := by simpa only [interior_Ioi, Set.mem_Ioi] using hx
    rw [(collisionScaleDifference_deriv gamma k x hg hk hx0).deriv]
    have hkg : 0 < k * gamma := mul_pos (lt_trans (by norm_num) hk) hg
    have ha : 0 < 1 + gamma * x := by positivity
    have hb : 0 < 1 + k * gamma * x := by positivity
    have hden : 1 + gamma * x < 1 + k * gamma * x := by
      nlinarith [mul_pos (sub_pos.mpr hk) (mul_pos hg hx0)]
    have hdiv := (div_lt_div_iff₀ hb ha).mpr (mul_lt_mul_of_pos_left hden hkg)
    have he : k * (gamma / (1 + gamma * x)) = k * gamma / (1 + gamma * x) := by ring
    rw [he]
    linarith

theorem every_placed_collision_breaks_multiplication (mu gamma c n m k : ℝ)
    (hg : 0 < gamma) (hm : 0 < m) (hmn : m < n) (hk : 1 < k)
    (hcol : placedCode mu gamma c n = placedCode mu gamma c m) :
    placedCode mu gamma c (k * n) < placedCode mu gamma c (k * m) := by
  have hs := collisionScaleDifference_strictAnti gamma k hg hk hm
    (lt_trans hm hmn) hmn
  unfold collisionScaleDifference at hs
  unfold placedCode at *
  have hnlog : 1 + gamma * (k * n) = 1 + k * gamma * n := by ring
  have hmlog : 1 + gamma * (k * m) = 1 + k * gamma * m := by ring
  rw [hnlog, hmlog]
  nlinarith

theorem intrinsic_alternative_strictAnti :
    StrictAnti (fun n : ℕ => SigmaPresentations.H ((n : ℝ) + 2)) := by
  have hh : StrictAntiOn SigmaPresentations.H (Set.Ioi 1) := by
    have hd : ∀ x : ℝ, 1 < x → HasDerivAt SigmaPresentations.H (1 / x - 1) x := by
      intro x hx
      simpa [SigmaPresentations.H] using
        ((Real.hasDerivAt_log (ne_of_gt (by linarith : 0 < x))).sub
          (hasDerivAt_id x)).add_const 1
    apply strictAntiOn_of_deriv_neg (convex_Ioi 1)
    · intro x hx
      exact (hd x hx).continuousAt.continuousWithinAt
    · intro x hx
      have hx1 : 1 < x := by simpa only [interior_Ioi, Set.mem_Ioi] using hx
      rw [(hd x hx1).deriv]
      have hi : 1 / x < 1 := (div_lt_one (by linarith)).mpr hx1
      linarith
  intro m n hmn
  apply hh (show (m : ℝ) + 2 ∈ Set.Ioi 1 from by
    change 1 < (m : ℝ) + 2
    have h := Nat.cast_nonneg (α := ℝ) m
    linarith)
    (show (n : ℝ) + 2 ∈ Set.Ioi 1 from by
      change 1 < (n : ℝ) + 2
      have h := Nat.cast_nonneg (α := ℝ) n
      linarith)
  exact_mod_cast (show m + 2 < n + 2 by omega)

theorem intrinsic_alternative_injective :
    Function.Injective (fun n : ℕ => SigmaPresentations.H ((n : ℝ) + 2)) :=
  intrinsic_alternative_strictAnti.injective

section Transport
variable {A B : Type*} [CommMonoid A] (e : A → B) (he : Function.Injective e)

def transportedProduct (x y : Set.range e) : Set.range e :=
  Equiv.ofInjective e he ((Equiv.ofInjective e he).symm x *
    (Equiv.ofInjective e he).symm y)

def transportedUnit : Set.range e := Equiv.ofInjective e he 1

theorem transportedProduct_encode (a b : A) :
    transportedProduct e he (Equiv.ofInjective e he a) (Equiv.ofInjective e he b) =
      Equiv.ofInjective e he (a * b) := by simp [transportedProduct]

theorem transportedProduct_assoc (x y z : Set.range e) :
    transportedProduct e he (transportedProduct e he x y) z =
      transportedProduct e he x (transportedProduct e he y z) := by
  simp [transportedProduct, mul_assoc]

theorem transportedProduct_comm (x y : Set.range e) :
    transportedProduct e he x y = transportedProduct e he y x := by
  simp [transportedProduct, mul_comm]

theorem transportedUnit_mul (x : Set.range e) :
    transportedProduct e he (transportedUnit e he) x = x := by
  simp [transportedProduct, transportedUnit]

theorem transported_divisibility (a b : A) :
    (∃ z : Set.range e,
      transportedProduct e he (Equiv.ofInjective e he a) z = Equiv.ofInjective e he b)
        ↔ a ∣ b := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨(Equiv.ofInjective e he).symm z, ?_⟩
    have h := congrArg (Equiv.ofInjective e he).symm hz
    simpa [transportedProduct] using h.symm
  · rintro ⟨z, rfl⟩
    exact ⟨Equiv.ofInjective e he z, transportedProduct_encode e he a z⟩

end Transport
end
end Sigma
