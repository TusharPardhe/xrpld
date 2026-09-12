import XRPL.Model.Lending.LoanBroker.LoanBroker
import XRPL.Model.Protocol.TenthBips

/-! # Loan broker state validity

`WF` checks the stored `Number` fields are normalized. `Exact.Valid` states
 the invariant in exact rationals. `Valid` states the same invariant with the `Number`
operators the code compares with. A `Lawful` state is both well-formed and valid. -/

namespace XRPL.Model.Lending

open XRPL.Model.Protocol

/-- The broker state in exact arithmetic, retaining its stable identity. -/
structure LoanBroker.Exact where
  identity : BrokerIdentity
  debtTotal : ℚ
  debtMaximum : ℚ
  coverAvailable : ℚ
  managementFeeRate : ℕ
  coverRateMinimum : ℕ
  coverRateLiquidation : ℕ
  loanCount : ℕ

/-- The exact value of a broker state. -/
def LoanBroker.toExact (lb : LoanBroker) : LoanBroker.Exact where
  identity := lb.identity
  debtTotal := lb.debtTotal.toRat
  debtMaximum := lb.debtMaximum.toRat
  coverAvailable := lb.coverAvailable.toRat
  managementFeeRate := lb.managementFeeRate.toNat
  coverRateMinimum := lb.coverRateMinimum.toNat
  coverRateLiquidation := lb.coverRateLiquidation.toNat
  loanCount := lb.loanCount.toNat

/-- Representation well-formed: every stored amount is a normalized `Number`.
The rates and loan count are integers, so they need no extra clause. -/
structure LoanBroker.WF (lb : LoanBroker) : Prop where
  debtTotal_norm : lb.debtTotal.isNormalized
  debtMaximum_norm : lb.debtMaximum.isNormalized
  coverAvailable_norm : lb.coverAvailable.isNormalized

instance LoanBroker.instDecidableWF (lb : LoanBroker) : Decidable lb.WF :=
  decidable_of_iff
    (lb.debtTotal.isNormalized ∧ lb.debtMaximum.isNormalized ∧ lb.coverAvailable.isNormalized)
    ⟨fun ⟨debtTotal_norm, debtMaximum_norm, coverAvailable_norm⟩ =>
        ⟨debtTotal_norm, debtMaximum_norm, coverAvailable_norm⟩,
      fun h => ⟨h.debtTotal_norm, h.debtMaximum_norm, h.coverAvailable_norm⟩⟩

/-- The broker invariant in exact arithmetic. -/
structure LoanBroker.Exact.Valid (s : LoanBroker.Exact) : Prop where
  identity_wellFormed : s.identity.wellFormed = true
  debtTotal_nonneg : 0 ≤ s.debtTotal
  debtMaximum_nonneg : 0 ≤ s.debtMaximum
  coverAvailable_nonneg : 0 ≤ s.coverAvailable
  debtMaximum_cap : s.debtMaximum ≤ (2 : ℚ) ^ 63 - 1
  debt_within_cap : s.debtMaximum ≠ 0 → s.debtTotal ≤ s.debtMaximum
  cover_floor : s.debtTotal * (s.coverRateMinimum : ℚ) ≤ 100000 * s.coverAvailable
  empty_broker : s.loanCount = 0 → s.debtTotal = 0
  mgmtFee_cap : s.managementFeeRate ≤ maxManagementFeeRate
  coverMin_cap : s.coverRateMinimum ≤ maxCoverRate
  coverLiq_cap : s.coverRateLiquidation ≤ maxCoverRate
  rate_coupling : s.coverRateMinimum = 0 ↔ s.coverRateLiquidation = 0

instance LoanBroker.Exact.instDecidableValid (s : LoanBroker.Exact) : Decidable s.Valid :=
  decidable_of_iff
    (s.identity.wellFormed = true ∧
      0 ≤ s.debtTotal ∧ 0 ≤ s.debtMaximum ∧ 0 ≤ s.coverAvailable ∧
      s.debtMaximum ≤ (2 : ℚ) ^ 63 - 1 ∧
      (s.debtMaximum ≠ 0 → s.debtTotal ≤ s.debtMaximum) ∧
      s.debtTotal * (s.coverRateMinimum : ℚ) ≤ 100000 * s.coverAvailable ∧
      (s.loanCount = 0 → s.debtTotal = 0) ∧
      s.managementFeeRate ≤ maxManagementFeeRate ∧ s.coverRateMinimum ≤ maxCoverRate ∧
      s.coverRateLiquidation ≤ maxCoverRate ∧
      (s.coverRateMinimum = 0 ↔ s.coverRateLiquidation = 0))
    ⟨fun ⟨identity_wellFormed, debtTotal_nonneg, debtMaximum_nonneg, coverAvailable_nonneg,
        debtMaximum_cap, debt_within_cap, cover_floor, empty_broker, mgmtFee_cap,
        coverMin_cap, coverLiq_cap, rate_coupling⟩ =>
        ⟨identity_wellFormed, debtTotal_nonneg, debtMaximum_nonneg, coverAvailable_nonneg,
          debtMaximum_cap, debt_within_cap, cover_floor, empty_broker, mgmtFee_cap,
          coverMin_cap, coverLiq_cap, rate_coupling⟩,
      fun h => ⟨h.identity_wellFormed, h.debtTotal_nonneg, h.debtMaximum_nonneg,
        h.coverAvailable_nonneg, h.debtMaximum_cap, h.debt_within_cap, h.cover_floor,
        h.empty_broker, h.mgmtFee_cap, h.coverMin_cap, h.coverLiq_cap, h.rate_coupling⟩⟩

/-- `LoanBroker.Exact.Valid`, restated with the modeled `Number` operators on the
stored fields. -/
structure LoanBroker.Valid (lb : LoanBroker) : Prop where
  identity_wellFormed : lb.identity.wellFormed = true
  debtTotal_nonneg : Number.zero.operator_le lb.debtTotal = true
  debtMaximum_nonneg : Number.zero.operator_le lb.debtMaximum = true
  coverAvailable_nonneg : Number.zero.operator_le lb.coverAvailable = true
  debtMaximum_cap : lb.debtMaximum.operator_le debtMaxCap = true
  debt_within_cap : lb.debtMaximum ≠ Number.zero →
    lb.debtTotal.operator_le lb.debtMaximum = true
  cover_floor : ∀ lhs rhs,
    lb.debtTotal.operator_mul lb.coverRateMinimum.toNumber .upward = .ok lhs →
    lb.coverAvailable.operator_mul kTenthBipsPerUnity.toNumber .to_nearest = .ok rhs →
    lhs.operator_le rhs = true
  empty_broker : lb.loanCount = 0 → lb.debtTotal = Number.zero
  mgmtFee_cap : lb.managementFeeRate.toNat ≤ maxManagementFeeRate
  coverMin_cap : lb.coverRateMinimum.toNat ≤ maxCoverRate
  coverLiq_cap : lb.coverRateLiquidation.toNat ≤ maxCoverRate
  rate_coupling : lb.coverRateMinimum.toNat = 0 ↔ lb.coverRateLiquidation.toNat = 0

/-- A lawful broker is a well-formed representation whose exact value satisfies
 the invariant. -/
structure LoanBroker.Lawful (lb : LoanBroker) : Prop where
  wf : lb.WF
  valid : lb.toExact.Valid

instance LoanBroker.instDecidableLawful (lb : LoanBroker) : Decidable lb.Lawful :=
  decidable_of_iff (lb.WF ∧ lb.toExact.Valid)
    ⟨fun ⟨wf, valid⟩ => ⟨wf, valid⟩, fun h => ⟨h.wf, h.valid⟩⟩

/-- A broker bundled with its lawfulness proof. -/
def LawfulLoanBroker : Type := {lb : LoanBroker // lb.Lawful}

/-- Raw broker of a lawful broker. -/
def LawfulLoanBroker.val (lb : LawfulLoanBroker) : LoanBroker := Subtype.val lb

/-- Lawfulness proof of a lawful broker. -/
def LawfulLoanBroker.lawful (lb : LawfulLoanBroker) : lb.val.Lawful := Subtype.property lb

/-- The untrusted-boundary check: promote a raw broker to a `LawfulLoanBroker` if it
is lawful. Its derived `Decidable` instance keeps the boundary executable. -/
def LoanBroker.validate (lb : LoanBroker) : Option LawfulLoanBroker :=
  if h : lb.Lawful then some ⟨lb, h⟩ else none

end XRPL.Model.Lending
