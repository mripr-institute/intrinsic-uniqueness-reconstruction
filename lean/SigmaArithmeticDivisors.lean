import SigmaArithmeticInventory
import Mathlib.Data.Multiset.Interval
import Mathlib.Algebra.Prime.Lemmas
import Mathlib.Data.Finite.Card

namespace Sigma
noncomputable section
open Set
open scoped BigOperators

theorem pnat_isUnit_iff_one (n : ℕ+) : IsUnit n ↔ n=1 := by
  constructor
  · intro h
    apply Subtype.ext
    obtain ⟨u, rfl⟩ := h
    exact Nat.eq_one_of_dvd_one (PNat.dvd_iff.mp ⟨↑u⁻¹, u.val_inv.symm⟩)
  · rintro rfl
    exact isUnit_one

theorem pnat_irreducible_iff_prime (n : ℕ+) : Irreducible n ↔ n.Prime := by
  constructor
  · intro hn
    obtain ⟨p,hp,hpn⟩ := PNat.exists_prime_and_dvd hn.ne_one
    obtain ⟨k,hk⟩ := hpn
    rcases hn.isUnit_or_isUnit hk with h | h
    · exact False.elim (hp.ne_one ((pnat_isUnit_iff_one p).mp h))
    · have hk1 := (pnat_isUnit_iff_one k).mp h
      simpa [hk, hk1] using hp
  · intro hn
    refine ⟨fun h => hn.ne_one ((pnat_isUnit_iff_one n).mp h), ?_⟩
    intro a b hab
    have ha : a ∣ n := ⟨b,hab⟩
    rcases (PNat.dvd_prime hn).mp ha with ha | ha
    · exact Or.inl ((pnat_isUnit_iff_one a).mpr ha)
    · right
      apply (pnat_isUnit_iff_one b).mpr
      apply mul_left_cancel (a:=n)
      simpa [ha] using hab.symm

section Inventory
variable {M : Type*} [CommMonoid M] (E : ℕ+ ≃* M)

theorem labelled_irreducible_iff (x : M) :
    Irreducible x ↔ ∃ p : Nat.Primes, x=E (p : ℕ+) := by
  rw [← E.apply_symm_apply x, MulEquiv.irreducible_iff E, pnat_irreducible_iff_prime]
  constructor
  · intro h
    exact ⟨⟨(E.symm x).val,h⟩,rfl⟩
  · rintro ⟨p,hp⟩
    have h := E.injective hp
    exact h.symm ▸ p.property

def labelledOmega (x : M) : ℕ := (labelledFactors E x).card
def labelledLittleOmega (x : M) : ℕ := (labelledFactors E x).toFinset.card

theorem labelled_factor_count (x : M) :
    labelledOmega E x=∑ p ∈ (labelledFactors E x).toFinset, labelledValuation E p x :=
  (Multiset.toFinset_sum_count_eq _).symm

theorem labelled_valuation_support (x : M) (p : Nat.Primes) :
    p ∈ (labelledFactors E x).toFinset ↔ 0 < labelledValuation E p x := by
  exact Multiset.mem_toFinset.trans Multiset.count_pos.symm

theorem labelled_distinct_factor_count (x : M) :
    labelledLittleOmega E x=Nat.card {p : Nat.Primes // 0 < labelledValuation E p x} := by
  unfold labelledLittleOmega
  rw [← Nat.card_eq_finsetCard]
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (labelled_valuation_support E x)

/-- An actual finite enumeration of the divisors. -/
def labelledDivisors (x : M) : Finset M :=
  (@Finset.Iic (Multiset Nat.Primes) _ _ (labelledFactors E x)).map
    ⟨fun s => E (PrimeMultiset.prod s), by
      intro a b h
      have h' := congrArg PNat.factorMultiset (E.injective h)
      simpa only [PrimeMultiset.factorMultiset_prod] using h'⟩

theorem mem_labelled_divisors (x d : M) : d ∈ labelledDivisors E x ↔ d ∣ x := by
  classical
  constructor
  · intro h
    obtain ⟨s,hs,rfl⟩ := Finset.mem_map.mp h
    rw [labelled_dvd_iff_factors E]
    change labelledFactors E (E s.prod) ≤ labelledFactors E x
    rw [labelled_factorization_unique]
    simpa only [Finset.mem_Iic] using hs
  · intro h
    apply Finset.mem_map.mpr
    refine ⟨labelledFactors E d, ?_, labelled_factorization_inverse E d⟩
    simpa only [Finset.mem_Iic] using (labelled_dvd_iff_factors E d x).mp h

theorem labelled_divisor_count (x : M) :
    (labelledDivisors E x).card=
      ∏ p ∈ (labelledFactors E x).toFinset, (labelledValuation E p x+1) := by
  unfold labelledDivisors
  rw [Finset.card_map]
  exact Multiset.card_Iic _

end Inventory
end
end Sigma
