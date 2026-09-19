import SigmaRealArithmetic
import Mathlib.Data.PNat.Basic
import Mathlib.Algebra.Group.WithOne.Basic
import Mathlib.Logic.Equiv.TransferInstance

namespace Sigma
noncomputable section
open Set

/-- The original integer carrier excludes the unit index. -/
def IntegerCodeIndex := {n : ℕ // 2 ≤ n}

instance : CommSemigroup IntegerCodeIndex where
  mul a b := ⟨a.val*b.val, by have := a.property; have := b.property; nlinarith⟩
  mul_assoc a b c := Subtype.ext (Nat.mul_assoc _ _ _)
  mul_comm a b := Subtype.ext (Nat.mul_comm _ _)

@[simp] theorem integer_code_mul_val (a b : IntegerCodeIndex) :
    (a*b).val=a.val*b.val := rfl

def placedIntegerCode (μ γ c : ℝ) (n : IntegerCodeIndex) : ℝ :=
  placedCode μ γ c n.val

def codeImagePoint {A B : Type*} (e : A → B) (a : A) : range e := ⟨e a, ⟨a,rfl⟩⟩

/-- Existence of the prescribed operation is necessary, not just sufficient,
for injectivity on the exact n>=2 carrier. -/
theorem placed_integer_operation_iff (μ γ c : ℝ) (hγ : 0 < γ) :
    (∃ op : range (placedIntegerCode μ γ c) → range (placedIntegerCode μ γ c) →
        range (placedIntegerCode μ γ c),
      ∀ a b : IntegerCodeIndex,
        op (codeImagePoint (placedIntegerCode μ γ c) a)
          (codeImagePoint (placedIntegerCode μ γ c) b)=
            codeImagePoint (placedIntegerCode μ γ c) (a*b)) ↔
      Function.Injective (placedIntegerCode μ γ c) := by
  constructor
  · rintro ⟨op,hop⟩ a b hab
    let k : IntegerCodeIndex := ⟨2,le_rfl⟩
    have he : codeImagePoint (placedIntegerCode μ γ c) a=
        codeImagePoint (placedIntegerCode μ γ c) b := Subtype.ext hab
    have hm := congrArg (fun z => op (codeImagePoint (placedIntegerCode μ γ c) k) z) he
    dsimp only at hm
    rw [hop, hop] at hm
    have hm' := congrArg Subtype.val hm
    simp only [codeImagePoint, placedIntegerCode, integer_code_mul_val, k,
      Nat.cast_mul, Nat.cast_ofNat] at hm'
    change placedCode μ γ c a.val=placedCode μ γ c b.val at hab
    apply Subtype.ext
    rcases lt_trichotomy a.val b.val with h | h | h
    · have hh := every_placed_collision_breaks_multiplication μ γ c b.val a.val 2 hγ
        (by exact_mod_cast (show 0 < a.val from by have := a.property; omega))
        (by exact_mod_cast h) (by norm_num) hab.symm
      linarith
    · exact h
    · have hh := every_placed_collision_breaks_multiplication μ γ c a.val b.val 2 hγ
        (by exact_mod_cast (show 0 < b.val from by have := b.property; omega))
        (by exact_mod_cast h) (by norm_num) hab
      linarith
  · intro he
    let E := Equiv.ofInjective (placedIntegerCode μ γ c) he
    refine ⟨fun x y => E (E.symm x*E.symm y), ?_⟩
    intro a b
    change E (E.symm (E a)*E.symm (E b))=E (a*b)
    rw [E.symm_apply_apply, E.symm_apply_apply]

def integerCodeToPositive : IntegerCodeIndex →ₙ* ℕ+ where
  toFun n := ⟨n.val, by have := n.property; omega⟩
  map_mul' _ _ := rfl

theorem integer_code_unit_extension_bijective :
    Function.Bijective (WithOne.lift integerCodeToPositive) := by
  constructor
  · intro a b hab
    induction a using WithOne.recOneCoe with
    | h₁ =>
      induction b using WithOne.recOneCoe with
      | h₁ => rfl
      | h₂ b =>
        have he := congrArg (fun n : ℕ+ => n.val) hab
        change 1=b.val at he
        have := b.property
        omega
    | h₂ a =>
      induction b using WithOne.recOneCoe with
      | h₁ =>
        have he := congrArg (fun n : ℕ+ => n.val) hab
        change a.val=1 at he
        have := a.property
        omega
      | h₂ b =>
        have he := congrArg (fun n : ℕ+ => n.val) hab
        have he' : a=b := Subtype.ext he
        rw [he']
  · intro n
    by_cases hn : n.val=1
    · refine ⟨1, ?_⟩
      apply Subtype.ext
      exact hn.symm
    · have hn2 : 2 ≤ n.val := Nat.succ_le_of_lt
        (lt_of_le_of_ne (Nat.succ_le_of_lt n.property) (Ne.symm hn))
      exact ⟨WithOne.coe (⟨n.val,hn2⟩ : IntegerCodeIndex), rfl⟩

/-- Adjoining an abstract unit to precisely the n>=2 semigroup gives the
positive integers, with their ordinary multiplication. -/
def integerCodeUnitEquiv : WithOne IntegerCodeIndex ≃* ℕ+ :=
  MulEquiv.ofBijective (WithOne.lift integerCodeToPositive) integer_code_unit_extension_bijective

/-- The image with a separate abstract unit, not the possibly colliding real
value at index one, is the labelled positive-integer monoid. -/
def labelledImageEquiv {B : Type*} (e : IntegerCodeIndex → B) (he : Function.Injective e) :
    letI := (Equiv.ofInjective e he).symm.commSemigroup
    ℕ+ ≃* WithOne (range e) := by
  letI := (Equiv.ofInjective e he).symm.commSemigroup
  exact integerCodeUnitEquiv.symm.trans ((Equiv.ofInjective e he).symm.mulEquiv.symm.withOneCongr)

theorem labelled_image_unit_separate {B : Type*} (e : IntegerCodeIndex → B)
    (x : range e) : (x : WithOne (range e)) ≠ 1 := WithOne.coe_ne_one

theorem labelled_image_encode {B : Type*} (e : IntegerCodeIndex → B)
    (he : Function.Injective e) (a : IntegerCodeIndex) :
    letI := (Equiv.ofInjective e he).symm.commSemigroup
    labelledImageEquiv e he (integerCodeToPositive a)=
      WithOne.coe (codeImagePoint e a) := by
  letI := (Equiv.ofInjective e he).symm.commSemigroup
  have ha : integerCodeToPositive a=integerCodeUnitEquiv (WithOne.coe a) := rfl
  rw [ha]
  change ((Equiv.ofInjective e he).symm.mulEquiv.symm.withOneCongr)
    (integerCodeUnitEquiv.symm (integerCodeUnitEquiv (WithOne.coe a)))=_
  rw [integerCodeUnitEquiv.symm_apply_apply]
  rfl

theorem placed_shifted_integer_sampling (μ γ c : ℝ) (hμ : 0 < μ) (hγ : 0 < γ)
    (n : ℕ) :
    placedCode μ γ c (1/μ-1/γ+n/μ)=
      SigmaPresentations.H (n+1)+Real.log (γ/μ)+μ/γ-1+c := by
  have he : 1+γ*(1/μ-1/γ+n/μ)=(γ/μ)*(n+1) := by
    field_simp
    ring
  unfold placedCode SigmaPresentations.H
  rw [he, Real.log_mul (div_ne_zero hγ.ne' hμ.ne') (by positivity : (n+1:ℝ) ≠ 0)]
  field_simp
  ring

end
end Sigma
