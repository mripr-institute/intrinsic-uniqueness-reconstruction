import SigmaOpDeterminantHilbertSchmidt
import SigmaOpDeterminantCanonical

namespace Sigma
noncomputable section
universe u v
variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The corresponding shifted Schatten category, stated entirely in native
operator terms: a nonnegative self-adjoint generator whose genuine resolvent
has nuclear square. This is trace class for the squared shift and Schatten two
for the first shift. No spectral basis or determinant conclusion is assumed. -/
structure NativeShiftedDeterminantClass (A : H →ₗ.[ℂ] H) where
  selfadjoint : IsSelfAdjoint A
  nonnegative : ∀ x : A.domain, 0 ≤ (@inner ℂ H _ x.val (A x)).re
  resolvent : H →L[ℂ] H
  inverse : OpIsResolvent A 1 resolvent
  nuclear_square : IsNuclearOperator (resolvent^2)

/-- Spectral data derived from the native category. -/
structure NativeDeterminantSpectralData (A : H →ₗ.[ℂ] H) where
  index : Type u
  basis : HilbertBasis index ℂ H
  eigenvalue : index → ℝ
  nonnegative : ∀ i, 0 ≤ eigenvalue i
  domain : ∀ i, basis i ∈ A.domain
  action : ∀ i, A ⟨basis i, domain i⟩ = (eigenvalue i : ℂ) • basis i

def nativeDeterminantSpectralData {A : H →ₗ.[ℂ] H} (hA : NativeShiftedDeterminantClass A) :
    NativeDeterminantSpectralData A := by
  have hc := determinant_selfadjoint_compact_of_square hA.resolvent
    (selfadjoint_positive_shift_resolvent A hA.selfadjoint hA.resolvent hA.inverse)
    (determinant_nuclear_compact _ hA.nuclear_square)
  have he := nonnegative_compact_resolvent_eigenbasis A hA.selfadjoint hA.nonnegative
    hA.resolvent hA.inverse hc
  exact ⟨he.choose, he.choose_spec.choose, he.choose_spec.choose_spec.choose,
    he.choose_spec.choose_spec.choose_spec.1,
    he.choose_spec.choose_spec.choose_spec.2.choose,
    he.choose_spec.choose_spec.choose_spec.2.choose_spec⟩

/-- The ordinary (`false`) or regularized (`true`) determinant of a native shifted
operator, using a derived spectral basis. Choice independence is proved below. -/
def nativeShiftedDeterminant {A : H →ₗ.[ℂ] H} (hA : NativeShiftedDeterminantClass A)
    (reg : Bool) : ℂ → ℂ :=
  shiftedSpectralDeterminant reg (nativeDeterminantSpectralData hA).eigenvalue

theorem native_shifted_determinant_eq_spectral {A : H →ₗ.[ℂ] H}
    (hA : NativeShiftedDeterminantClass A) (reg : Bool)
    {ι : Type*} (b : HilbertBasis ι ℂ H) (lam : ι → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hdom : ∀ i, b i ∈ A.domain)
    (ha : ∀ i, A ⟨b i, hdom i⟩ = (lam i : ℂ) • b i) :
    nativeShiftedDeterminant hA reg = shiftedSpectralDeterminant reg lam := by
  let d := nativeDeterminantSpectralData hA
  exact native_shifted_determinant_basis_independent reg d.basis b d.eigenvalue lam
    d.nonnegative hlam A hA.selfadjoint hA.resolvent hA.inverse d.domain hdom d.action ha
    hA.nuclear_square

/-- Independence of the native category witness as well as the spectral basis. -/
theorem native_shifted_determinant_choice_independent {A : H →ₗ.[ℂ] H}
    (hA hA' : NativeShiftedDeterminantClass A) (reg : Bool) :
    nativeShiftedDeterminant hA reg = nativeShiftedDeterminant hA' reg := by
  let d := nativeDeterminantSpectralData hA'
  exact native_shifted_determinant_eq_spectral hA reg d.basis d.eigenvalue d.nonnegative
    d.domain d.action

theorem native_shifted_determinant_entire {A : H →ₗ.[ℂ] H}
    (hA : NativeShiftedDeterminantClass A) (reg : Bool) (z : ℂ) :
    AnalyticAt ℂ (nativeShiftedDeterminant hA reg) z := by
  let d := nativeDeterminantSpectralData hA
  exact spectral_determinant_entire reg _
    (native_shifted_determinant_summable reg d.basis d.eigenvalue d.nonnegative
      A hA.resolvent hA.inverse d.domain d.action hA.nuclear_square) z

/-- Full zero-multiset reconstruction for arbitrary nonnegative competing native
operators in the corresponding shifted Schatten category. -/
theorem native_shifted_determinant_zero_multiset_unique
    {A : H →ₗ.[ℂ] H} {B : K →ₗ.[ℂ] K}
    (hA : NativeShiftedDeterminantClass A) (hB : NativeShiftedDeterminantClass B)
    (reg : Bool)
    (hzeros : ∀ z : ℂ, (native_shifted_determinant_entire hA reg z).order =
      (native_shifted_determinant_entire hB reg z).order) :
    ∃ U : H ≃ₗᵢ[ℂ] K,
      (∀ x : H, U x ∈ B.domain ↔ x ∈ A.domain) ∧
      (∀ (x : A.domain) (y : B.domain), U x.val = y.val → U (A x) = B y) := by
  let d := nativeDeterminantSpectralData hA
  let e := nativeDeterminantSpectralData hB
  obtain ⟨_, _, U, _, hdom, ha⟩ := native_shifted_determinant_zeros_recover_operator reg
    d.basis e.basis d.eigenvalue e.eigenvalue d.nonnegative e.nonnegative
    A B hA.selfadjoint hB.selfadjoint hA.resolvent hB.resolvent hA.inverse hB.inverse
    d.domain e.domain d.action e.action hA.nuclear_square hB.nuclear_square hzeros
  exact ⟨U, hdom, ha⟩

/-- The conventional basis-image definition of Hilbert--Schmidt membership
implies the native determinant category. -/
def NativeShiftedDeterminantClass.ofHilbertSchmidt (A : H →ₗ.[ℂ] H)
    (hself : IsSelfAdjoint A)
    (hpos : ∀ x : A.domain, 0 ≤ (@inner ℂ H _ x.val (A x)).re)
    (R : H →L[ℂ] H) (hR : OpIsResolvent A 1 R) (hHS : IsHilbertSchmidtOperator R) :
    NativeShiftedDeterminantClass A :=
  ⟨hself, hpos, R, hR, determinant_hilbert_schmidt_square_nuclear R
    (selfadjoint_positive_shift_resolvent A hself R hR) hHS⟩

end
end Sigma
